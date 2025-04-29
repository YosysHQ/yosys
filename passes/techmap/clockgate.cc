#include "kernel/yosys.h"
#include "kernel/ff.h"
#include "kernel/gzip.h"
#include "libparse.h"
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ClockGateCell {
	IdString name;
	IdString ce_pin;
	IdString clk_in_pin;
	IdString clk_out_pin;
	std::vector<IdString> tie_lo_pins;
};

ClockGateCell icg_from_arg(std::string& name, std::string& str) {
	ClockGateCell c;
	c.name = RTLIL::escape_id(name);
	char delimiter = ':';
	size_t pos1 = str.find(delimiter);
	if (pos1 == std::string::npos)
		log_cmd_error("Not enough ports in descriptor string");
	size_t pos2 = str.find(delimiter, pos1 + 1);
	if (pos2 == std::string::npos)
		log_cmd_error("Not enough ports in descriptor string");
	size_t pos3 = str.find(delimiter, pos2 + 1);
	if (pos3 != std::string::npos)
		log_cmd_error("Too many ports in descriptor string");

	std::string ce = str.substr(0, pos1);
	c.ce_pin = RTLIL::escape_id(ce);

	std::string clk_in = str.substr(pos1 + 1, pos2 - (pos1 + 1));
	c.clk_in_pin = RTLIL::escape_id(clk_in);

	std::string clk_out = str.substr(pos2 + 1, str.size() - (pos2 + 1));
	c.clk_out_pin = RTLIL::escape_id(clk_out);
	return c;
}

static std::pair<std::optional<ClockGateCell>, std::optional<ClockGateCell>>
	find_icgs(std::vector<const LibertyAst *> cells, std::vector<std::string> const& dont_use_cells) {
	// We will pick the most suitable ICG absed on tie_lo count and area
	struct ICGRankable : public ClockGateCell { double area; };
	std::optional<ICGRankable> best_pos;
	std::optional<ICGRankable> best_neg;

	// This is a lot of boilerplate, isn't it?
	for (auto cell : cells)
	{
		const LibertyAst *dn = cell->find("dont_use");
		if (dn != nullptr && dn->value == "true")
			continue;

		bool dont_use = false;
		for (auto dont_use_cell : dont_use_cells)
		{
			if (patmatch(dont_use_cell.c_str(), cell->args[0].c_str()))
			{
				dont_use = true;
				break;
			}
		}
		if (dont_use)
			continue;

		const LibertyAst *icg_kind_ast = cell->find("clock_gating_integrated_cell");
		if (icg_kind_ast == nullptr)
			continue;

		auto cell_name = cell->args[0];
		auto icg_kind = icg_kind_ast->value;
		auto starts_with = [&](std::string prefix) {
			return icg_kind.compare(0, prefix.size(), prefix) == 0;
		};
		bool clk_pol;
		if (icg_kind == "latch_posedge" || starts_with("latch_posedge_")) {
			clk_pol = true;
		} else if (icg_kind == "latch_negedge" || starts_with("latch_negedge_")) {
			clk_pol = false;
		} else {
			log("Ignoring ICG primitive %s of kind '%s'\n", cell_name.c_str(), icg_kind.c_str());
			continue;
		}

		log_debug("maybe valid icg: %s\n", cell_name.c_str());
		ClockGateCell icg_interface;
		icg_interface.name = RTLIL::escape_id(cell_name);

		for (auto pin : cell->children) {
			if (pin->id != "pin" || pin->args.size() != 1)
				continue;

			if (pin->find("clock_gate_clock_pin")) {
				if (!icg_interface.clk_in_pin.empty()) {
					log_warning("Malformed liberty file - multiple clock_gate_clock_pin in cell %s\n",
						cell_name.c_str());
					continue;
				} else
					icg_interface.clk_in_pin = RTLIL::escape_id(pin->args[0]);
			} else if (pin->find("clock_gate_out_pin")) {
				if (!icg_interface.clk_out_pin.empty()) {
					log_warning("Malformed liberty file - multiple clock_gate_out_pin in cell %s\n",
						cell_name.c_str());
					continue;
				} else
					icg_interface.clk_out_pin = RTLIL::escape_id(pin->args[0]);
			} else if (pin->find("clock_gate_enable_pin")) {
				if (!icg_interface.ce_pin.empty()) {
					log_warning("Malformed liberty file - multiple clock_gate_enable_pin in cell %s\n",
						cell_name.c_str());
					continue;
				} else
					icg_interface.ce_pin = RTLIL::escape_id(pin->args[0]);
			} else if (pin->find("clock_gate_test_pin")) {
				icg_interface.tie_lo_pins.push_back(RTLIL::escape_id(pin->args[0]));
			} else {
				const LibertyAst *dir = pin->find("direction");
				if (dir->value == "internal")
					continue;

				log_warning("Malformed liberty file - extra pin %s in cell %s\n",
					pin->args[0].c_str(), cell_name.c_str());
				continue;
			}
		}

		if (icg_interface.clk_in_pin.empty()) {
			log_warning("Malformed liberty file - missing clock_gate_clock_pin in cell %s",
				cell_name.c_str());
			continue;
		}
		if (icg_interface.clk_out_pin.empty()) {
			log_warning("Malformed liberty file - missing clock_gate_out_pin in cell %s",
				cell_name.c_str());
			continue;
		}
		if (icg_interface.ce_pin.empty()) {
			log_warning("Malformed liberty file - missing clock_gate_enable_pin in cell %s",
				cell_name.c_str());
			continue;
		}

		double area = 0;
		const LibertyAst *ar = cell->find("area");
		if (ar != nullptr && !ar->value.empty())
			area = atof(ar->value.c_str());

		std::optional<ICGRankable>& icg_to_beat = clk_pol ? best_pos : best_neg;

		bool winning = false;
		if (icg_to_beat) {
			log_debug("ties: %zu ? %zu\n", icg_to_beat->tie_lo_pins.size(),
				icg_interface.tie_lo_pins.size());
			log_debug("area: %f ? %f\n", icg_to_beat->area, area);

			// Prefer fewer test enables over area reduction (unlikely to matter)
			auto goal = std::make_pair(icg_to_beat->tie_lo_pins.size(), icg_to_beat->area);
			auto cost = std::make_pair(icg_interface.tie_lo_pins.size(), area);
			winning = cost < goal;

			if (winning)
				log_debug("%s beats %s\n", icg_interface.name.c_str(), icg_to_beat->name.c_str());
		} else {
			log_debug("%s is the first of its polarity\n", icg_interface.name.c_str());
			winning = true;
		}
		if (winning) {
			ICGRankable new_icg {icg_interface, area};
			icg_to_beat.emplace(new_icg);
		}
	}

	std::optional<ClockGateCell> pos;
	std::optional<ClockGateCell> neg;
	if (best_pos) {
		log("Selected rising edge ICG %s from Liberty file\n", best_pos->name.c_str());
		pos.emplace(*best_pos);
	}
	if (best_neg) {
		log("Selected falling edge ICG %s from Liberty file\n", best_neg->name.c_str());
		neg.emplace(*best_neg);
	}
	return std::make_pair(pos, neg);
}

struct ClockgatePass : public Pass {
	ClockgatePass() : Pass("clockgate", "extract clock gating out of flip flops") { }
	void help() override {
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clockgate [options] [selection]\n");
		log("\n");
		log("This pass transforms each set of FFs sharing the same clock and\n");
		log("enable signal into a clock-gating cell and a set of enable-less FFs.\n");
		log("Primarily a power-saving transformation on ASIC designs.\n");
		log("\n");
		log("    -pos <celltype> <ce>:<clk>:<gclk>\n");
		log("        If specified, rising-edge FFs will have CE inputs\n");
		log("        removed and a gated clock will be created by the\n");
		log("        user-specified <celltype> ICG (integrated clock gating)\n");
		log("        cell with ports named <ce>, <clk>, <gclk>.\n");
		log("        The ICG's clock enable pin must be active high.\n");
		log("    -neg <celltype> <ce>:<clk>:<gclk>\n");
		log("        If specified, falling-edge FFs will have CE inputs\n");
		log("        removed and a gated clock will be created by the\n");
		log("        user-specified <celltype> ICG (integrated clock gating)\n");
		log("        cell with ports named <ce>, <clk>, <gclk>.\n");
		log("        The ICG's clock enable pin must be active high.\n");
		log("    -liberty <filename>\n");
		log("        If specified, ICGs will be selected from the liberty files\n");
		log("        if available. Priority is given to cells with fewer tie_lo\n");
		log("        inputs and smaller size. This removes the need to manually\n");
		log("        specify -pos or -neg and -tie_lo.\n");
		log("    -dont_use <celltype>\n");
		log("        Cells <celltype> won't be considered when searching for ICGs\n");
		log("        in the liberty file specified by -liberty.\n");
		log("    -tie_lo <port_name>\n");
		log("        Port <port_name> of the ICG will be tied to zero.\n");
		log("        Intended for DFT scan-enable pins.\n");
		log("    -min_net_size <n>\n");
		log("        Only transform sets of at least <n> eligible FFs.\n");
		log("        \n");
	}

	// One ICG will be generated per ClkNetInfo
	// if the number of FFs associated with it is sufficent
	struct ClkNetInfo {
		// Original, ungated clock into enabled FF
		SigBit clk_bit;
		// Original clock enable into enabled FF
		SigBit ce_bit;
		bool pol_clk;
		bool pol_ce;
		[[nodiscard]] Hasher hash_into(Hasher h) const {
			auto t = std::make_tuple(clk_bit, ce_bit, pol_clk, pol_ce);
			h.eat(t);
			return h;
		}
		bool operator==(const ClkNetInfo& other) const {
			return (clk_bit == other.clk_bit) &&
			       (ce_bit == other.ce_bit) &&
			       (pol_clk == other.pol_clk) &&
			       (pol_ce == other.pol_ce);
		}
	};

	struct GClkNetInfo {
		// How many CE FFs on this CLK net have we seen?
		int net_size;
		// After ICG generation, we have new gated CLK signals
		Wire* new_net;
	};

	ClkNetInfo clk_info_from_ff(FfData& ff) {
		SigBit clk = ff.sig_clk[0];
		SigBit ce = ff.sig_ce[0];
		ClkNetInfo info{clk, ce, ff.pol_clk, ff.pol_ce};
		return info;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override {
		log_header(design, "Executing CLOCK_GATE pass (extract clock gating out of flip flops).\n");

		std::optional<ClockGateCell> pos_icg_desc;
		std::optional<ClockGateCell> neg_icg_desc;
		std::vector<std::string> tie_lo_pins;
		std::vector<std::string> liberty_files;
		std::vector<std::string> dont_use_cells;
		int min_net_size = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-pos" && argidx+2 < args.size()) {
				auto name = args[++argidx];
				auto rest = args[++argidx];
				pos_icg_desc = icg_from_arg(name, rest);
				continue;
			}
			if (args[argidx] == "-neg" && argidx+2 < args.size()) {
				auto name = args[++argidx];
				auto rest = args[++argidx];
				neg_icg_desc = icg_from_arg(name, rest);
				continue;
			}
			if (args[argidx] == "-tie_lo" && argidx+1 < args.size()) {
				tie_lo_pins.push_back(RTLIL::escape_id(args[++argidx]));
				continue;
			}
			if (args[argidx] == "-liberty" && argidx+1 < args.size()) {
				std::string liberty_file = args[++argidx];
				rewrite_filename(liberty_file);
				liberty_files.push_back(liberty_file);
				continue;
			}
			if (args[argidx] == "-dont_use" && argidx+1 < args.size()) {
				dont_use_cells.push_back(args[++argidx]);
				continue;
			}
			if (args[argidx] == "-min_net_size" && argidx+1 < args.size()) {
				min_net_size = atoi(args[++argidx].c_str());
				continue;
			}
			break;
		}

		if (!liberty_files.empty()) {
			LibertyMergedCells merged;
			for (auto path : liberty_files) {
				std::istream* f = uncompressed(path);
				LibertyParser p(*f, path);
				merged.merge(p);
				delete f;
			}
			std::tie(pos_icg_desc, neg_icg_desc) =
				find_icgs(merged.cells, dont_use_cells);
		} else {
			for (auto pin : tie_lo_pins) {
				if (pos_icg_desc)
					pos_icg_desc->tie_lo_pins.push_back(pin);
				if (neg_icg_desc)
					neg_icg_desc->tie_lo_pins.push_back(pin);
			}
		}

		extra_args(args, argidx, design);

		pool<Cell*> ce_ffs;
		dict<ClkNetInfo, GClkNetInfo> clk_nets;

		int gated_flop_count = 0;
		for (auto module : design->selected_unboxed_whole_modules()) {
			for (auto cell : module->cells()) {
				if (!RTLIL::builtin_ff_cell_types().count(cell->type))
					continue;

				FfData ff(nullptr, cell);
				// It would be odd to get constants, but we better handle it
				if (ff.has_ce) {
					if (!ff.sig_clk.is_bit() || !ff.sig_ce.is_bit())
						continue;
					if (!ff.sig_clk[0].is_wire() || !ff.sig_ce[0].is_wire())
						continue;

					ce_ffs.insert(cell);

					ClkNetInfo info = clk_info_from_ff(ff);
					auto it = clk_nets.find(info);
					if (it == clk_nets.end())
						clk_nets[info] = GClkNetInfo();
					clk_nets[info].net_size++;
				}
			}

			for (auto& clk_net : clk_nets) {
				auto& clk = clk_net.first;
				auto& gclk = clk_net.second;

				if (gclk.net_size < min_net_size)
					continue;

				std::optional<ClockGateCell> matching_icg_desc;

				if (pos_icg_desc && clk.pol_clk)
					matching_icg_desc = pos_icg_desc;
				else if (neg_icg_desc && !clk.pol_clk)
					matching_icg_desc = neg_icg_desc;

				if (!matching_icg_desc)
					continue;

				Cell* icg = module->addCell(NEW_ID, matching_icg_desc->name);
				icg->setPort(matching_icg_desc->ce_pin, clk.ce_bit);
				icg->setPort(matching_icg_desc->clk_in_pin, clk.clk_bit);
				gclk.new_net = module->addWire(NEW_ID);
				icg->setPort(matching_icg_desc->clk_out_pin, gclk.new_net);
				// Tie low DFT ports like scan chain enable
				for (auto port : matching_icg_desc->tie_lo_pins)
					icg->setPort(port, Const(0, 1));
				// Fix CE polarity if needed
				if (!clk.pol_ce) {
					SigBit ce_fixed_pol = module->NotGate(NEW_ID, clk.ce_bit);
					icg->setPort(matching_icg_desc->ce_pin, ce_fixed_pol);
				}
			}

			for (auto cell : ce_ffs) {
				FfData ff(nullptr, cell);
				ClkNetInfo info = clk_info_from_ff(ff);
				auto it = clk_nets.find(info);
				log_assert(it != clk_nets.end() && "Bug: desync ce_ffs and clk_nets");

				if (!it->second.new_net)
					continue;

				log_debug("Fix up FF %s\n", cell->name.c_str());
				// Now we start messing with the design
				ff.has_ce = false;
				// Construct the clock gate
				// ICG = integrated clock gate, industry shorthand
				ff.sig_clk = (*it).second.new_net;

				// Rebuild the flop
				(void)ff.emit();

				gated_flop_count++;
			}
			ce_ffs.clear();
			clk_nets.clear();
		}

		log("Converted %d FFs.\n", gated_flop_count);
    }
} ClockgatePass;


PRIVATE_NAMESPACE_END
