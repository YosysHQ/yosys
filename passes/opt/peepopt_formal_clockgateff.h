#ifndef PEEPOPT_FORMAL_CLOCKGATEFF_H
#define PEEPOPT_FORMAL_CLOCKGATEFF_H

#include "kernel/matcher.h"

YOSYS_NAMESPACE_BEGIN

// Detects the most common clock gating pattern using a latch and replaces it
// with a functionally equivalent pattern based on a flip-flop. The latch
// based pattern has a combinational path from the enable input to output after
// clk2fflogic, but this is a stable loop and the flip-flop based pattern does
// not exhibit this.
//
// This optimization is suitable for formal to prevent false comb loops, but
// should not be used for synthesis where the latch is an intentional choice
//
// Latch style:
// always @* if (!clk_i) latched_en = en;
// assign gated_clk_o = latched_en & clk_i;
//
// Flip-flop style:
// always @(posedge clk) flopped_en <= en;
// assign gated_clk_o = flopped_en & clk_i;

struct PeepoptFormalClockgateffMatch
{
	SigSpec clk = {};
	SigSpec en = {};
	SigSpec latched_en = {};
	SigSpec gated_clk = {};
	IdString latched_en_port_name = {};
	Cell *latch = nullptr;
	Cell *and_gate = nullptr;
};

struct PeepoptFormalClockgateff : MatchPattern<PeepoptFormalClockgateff, PeepoptFormalClockgateffMatch>
{
	struct AndGateChoice {
		Cell *cell = nullptr;
		IdString latch_port = {};
	};

	bool did_something = {};

	vector<Cell*> latch_cells = {};
	MatchIndex<std::tuple<SigSpec, SigSpec>, AndGateChoice> and_gate_index = {};

	PeepoptFormalClockgateff(MatchContext &ctx, const vector<Cell*> &cells) : MatchPattern(ctx, &PeepoptFormalClockgateff::match_latch)
	{
		for (auto cell : cells) {
			if (cell->type == ID($dlatch) && param(cell, ID::WIDTH) == 1 && param(cell, ID::EN_POLARITY).as_bool() == false)
				latch_cells.push_back(cell);
			if (cell->type.in(ID($and), ID($logic_and)) && param(cell, ID::A_WIDTH) == 1 && param(cell, ID::B_WIDTH) == 1 &&
					param(cell, ID::Y_WIDTH) == 1) {
				for (IdString clk_port : {ID::A, ID::B}) {
					IdString latch_port = (clk_port == ID::A ? ID::B : ID::A);
					and_gate_index.add({port(cell, clk_port), port(cell, latch_port)}, {cell, latch_port});
				}
			}
		}
	}

	void match_latch(const Match &m)
	{
		MatchFrame frame(ctx);
		for (Cell *latch : latch_cells) {
			if (blacklisted(latch))
				continue;
			Match n = m;
			n.latch = latch;
			n.clk = port(latch, ID::EN);
			n.en = port(latch, ID::D);
			n.latched_en = port(latch, ID::Q);
			frame.enter(latch);
			match_and_gate(n);
			if (frame.leave())
				return;
		}
	}

	void match_and_gate(const Match &m)
	{
		MatchFrame frame(ctx);
		for (auto &[and_gate, latch_port] : and_gate_index.find({m.clk, m.latched_en})) {
			if (blacklisted(and_gate))
				continue;
			Match n = m;
			n.and_gate = and_gate;
			n.gated_clk = port(and_gate, ID::Y);
			n.latched_en_port_name = latch_port;
			frame.enter(and_gate);
			code_replace(n);
			if (frame.leave())
				return;
		}
	}

	void code_replace(const Match &m)
	{
		log("replacing clock gate pattern in %s with ff: latch=%s, and=%s\n",
			module, m.latch, m.and_gate);

		// Add a flip-flop and rewire the AND gate to use the output of this flop
		// instead of the latch. We don't delete the latch in case its output is
		// used to drive other nodes. If it isn't, it will be trivially removed by
		// clean
		SigSpec flopped_en = module->addWire(NEW_ID);
		module->addDff(NEW_ID, m.clk, m.en, flopped_en, true, m.latch->get_src_attribute());
		m.and_gate->setPort(m.latched_en_port_name, flopped_en);
		did_something = true;

		accept(m);
	}
};

YOSYS_NAMESPACE_END

#endif
