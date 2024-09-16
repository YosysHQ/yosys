#include "kernel/yosys.h"
#include "kernel/ff.h"
#include <optional>

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct ClockGateCell {
	IdString name;
	IdString ce_pin;
	IdString clk_in_pin;
	IdString clk_out_pin;
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
		log("    -tie_lo <port_name>\n");
		log("        Port <port_name> of the ICG will be tied to zero.\n");
		log("        Intended for DFT scan-enable pins.\n");
		log("    -min_net_size <n>\n");
		log("        Only transform sets of at least <n> eligible FFs.\n");
		// log("        \n");
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
		unsigned int hash() const {
			auto t = std::make_tuple(clk_bit, ce_bit, pol_clk, pol_ce);
			unsigned int h = mkhash_init;
			h = mkhash(h, hash_ops<decltype(t)>::hash(t));
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
		std::vector<std::string> tie_lo_ports;
		int min_net_size = 0;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-pos" && argidx+2 < args.size()) {
				auto name = args[++argidx];
				auto rest = args[++argidx];
				pos_icg_desc = icg_from_arg(name, rest);
			}
			if (args[argidx] == "-neg" && argidx+2 < args.size()) {
				auto name = args[++argidx];
				auto rest = args[++argidx];
				neg_icg_desc = icg_from_arg(name, rest);
			}
			if (args[argidx] == "-tie_lo" && argidx+1 < args.size()) {
				tie_lo_ports.push_back(RTLIL::escape_id(args[++argidx]));
			}
			if (args[argidx] == "-min_net_size" && argidx+1 < args.size()) {
				min_net_size = atoi(args[++argidx].c_str());
			}
		}

		extra_args(args, argidx, design);

		pool<Cell*> ce_ffs;
		dict<ClkNetInfo, GClkNetInfo> clk_nets;

		int gated_flop_count = 0;
		for (auto module : design->selected_whole_modules()) {
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
				for (auto port : tie_lo_ports)
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
