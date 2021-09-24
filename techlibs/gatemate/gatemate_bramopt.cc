/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2021  Cologne Chip AG <support@colognechip.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

bool binary_pred(SigBit s1, SigBit s2)
{
	return s1 == s2;
}

static void proc_glwren(Module *module)
{
	std::vector<Cell*> ram_cells;

	// Gather RAM cells
	for (auto cell : module->cells())
	{
		if (cell->type.in(ID(CC_DPSRAM_20K), ID(CC_DPSRAM_40K))) {
			ram_cells.push_back(cell);
		}
	}

	// Convert bitmask signals
	for (auto cell : ram_cells)
	{
		std::vector<SigBit> mska = cell->getPort(ID(A_BM)).to_sigbit_vector();
		std::vector<SigBit> mskb = cell->getPort(ID(B_BM)).to_sigbit_vector();

		// Remove State::S0 from vectors
		mska.erase(std::remove_if(mska.begin(), mska.end(), [](const SigBit & sb){return (sb == State::S0);}), mska.end());
		mskb.erase(std::remove_if(mskb.begin(), mskb.end(), [](const SigBit & sb){return (sb == State::S0);}), mskb.end());

		if (mska.size() + mskb.size() == 0) {
			break;
		}

		if (cell->getParam(ID(RAM_MODE)).decode_string() == "SDP")
		{
			std::vector<SigBit> msk;
			msk.insert(msk.end(), mska.begin(), mska.end());
			msk.insert(msk.end(), mskb.begin(), mskb.end());

			if (std::equal(msk.begin() + 1, msk.end(), msk.begin(), binary_pred))
			{
				if ((cell->getPort(ID(A_WE)) == State::S1) && (cell->getPort(ID(B_WE)) == State::S0))
				{
					cell->setPort(ID(A_WE), msk[0]);
					cell->setPort(ID(B_WE), Const(0, 1));
					// Set bitmask bits to _1_
					cell->setPort(ID(A_BM), Const(State::S1, mska.size()));
					cell->setPort(ID(B_BM), Const(State::S1, mskb.size()));
				}
			}
		}
		else // RAM_MODE == "TDP"
		{
			if (std::equal(mska.begin() + 1, mska.end(), mska.begin(), binary_pred))
			{
				if (cell->getPort(ID(A_WE)) == State::S1)
				{
					// Signals are all equal
					cell->setPort(ID(A_WE), mska[0]);
					cell->setPort(ID(A_BM), Const(State::S1, mska.size()));
				}
			}
			if (std::equal(mskb.begin() + 1, mskb.end(), mskb.begin(), binary_pred))
			{
				if (cell->getPort(ID(B_WE)) == State::S1)
				{
					cell->setPort(ID(B_WE), mskb[0]);
					// Set bitmask bits to _1_
					cell->setPort(ID(B_BM), Const(State::S1, mskb.size()));
				}
			}
		}
	}
}

struct GateMateBramOptPass : public Pass {
	GateMateBramOptPass() : Pass("gatemate_bramopt", "GateMate: optimize block RAM cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    gatemate_bramopt [options] [selection]\n");
		log("\n");
		log("This pass processes all CC_BRAM_20K and CC_BRAM_40K cells and tries to");
		log("convert its enable bitmask wires to a single global enable signal.");
		log("\n");
		log("    -noglwren\n");
		log("        do not convert bitmasks to single global write enable signals.\n");
		log("\n");
	}

	bool noglwren;

	void clear_flags() override
	{
		noglwren = false;
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing GATEMATE_BRAMOPT pass (optimize block RAM).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-noglwren") {
				noglwren = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules())
		{
			if (!noglwren) {
				proc_glwren(module);
			}
		}
	}
} GateMateBramOptPass;

PRIVATE_NAMESPACE_END
