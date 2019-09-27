/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2018  David Shah <dave@ds0.me>
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

struct Dff2dffsPass : public Pass {
	Dff2dffsPass() : Pass("dff2dffs", "process sync set/reset with SR over CE priority") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    dff2dffs [options] [selection]\n");
		log("\n");
		log("Merge synchronous set/reset $_MUX_ cells to create $__DFFS_[NP][NP][01], to be run before\n");
		log("dff2dffe for SR over CE priority.\n");
		log("\n");
		log("    -match-init\n");
		log("        Disallow merging synchronous set/reset that has polarity opposite of the\n");
		log("        output wire's init attribute (if any).\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing dff2dffs pass (merge synchronous set/reset into FF cells).\n");

		bool match_init = false;
		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			// if (args[argidx] == "-singleton") {
			// 	singleton_mode = true;
			// 	continue;
			// }
			if (args[argidx] == "-match-init") {
				match_init = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		pool<IdString> dff_types;
		dff_types.insert(ID($_DFF_N_));
		dff_types.insert(ID($_DFF_P_));

		for (auto module : design->selected_modules())
		{
			log("Merging set/reset $_MUX_ cells into DFFs in %s.\n", log_id(module));

			SigMap sigmap(module);
			dict<SigBit, Cell*> sr_muxes;
			vector<Cell*> ff_cells;

			for (auto cell : module->selected_cells())
			{
				if (dff_types.count(cell->type)) {
					ff_cells.push_back(cell);
					continue;
				}

				if (cell->type != ID($_MUX_))
					continue;

				SigBit bit_a = sigmap(cell->getPort(ID::A));
				SigBit bit_b = sigmap(cell->getPort(ID::B));

				if (bit_a.wire == nullptr || bit_b.wire == nullptr)
					sr_muxes[sigmap(cell->getPort(ID::Y))] = cell;
			}

			for (auto cell : ff_cells)
			{
				SigSpec sig_d = cell->getPort(ID(D));

				if (GetSize(sig_d) < 1)
					continue;

				SigBit bit_d = sigmap(sig_d[0]);

				if (sr_muxes.count(bit_d) == 0)
					continue;

				Cell *mux_cell = sr_muxes.at(bit_d);
				SigBit bit_a = sigmap(mux_cell->getPort(ID::A));
				SigBit bit_b = sigmap(mux_cell->getPort(ID::B));
				SigBit bit_s = sigmap(mux_cell->getPort(ID(S)));

				SigBit sr_val, sr_sig;
				bool invert_sr;
				sr_sig = bit_s;
				if (bit_a.wire == nullptr) {
					bit_d = bit_b;
					sr_val = bit_a;
					invert_sr = true;
				} else {
					log_assert(bit_b.wire == nullptr);
					bit_d = bit_a;
					sr_val = bit_b;
					invert_sr = false;
				}

				if (match_init) {
					SigBit bit_q = cell->getPort(ID(Q));
					if (bit_q.wire) {
						auto it = bit_q.wire->attributes.find(ID(init));
						if (it != bit_q.wire->attributes.end()) {
							auto init_val = it->second[bit_q.offset];
							if (init_val == State::S1 && sr_val != State::S1)
								continue;
							if (init_val == State::S0 && sr_val != State::S0)
								continue;
						}
					}
				}

				log("  Merging %s (A=%s, B=%s, S=%s) into %s (%s).\n", log_id(mux_cell),
						log_signal(bit_a), log_signal(bit_b), log_signal(bit_s), log_id(cell), log_id(cell->type));

				if (sr_val == State::S1) {
					if (cell->type == ID($_DFF_N_)) {
						if (invert_sr) cell->type = ID($__DFFS_NN1_);
						else cell->type = ID($__DFFS_NP1_);
					} else {
						log_assert(cell->type == ID($_DFF_P_));
						if (invert_sr) cell->type = ID($__DFFS_PN1_);
						else cell->type = ID($__DFFS_PP1_);
					}
				} else {
					if (cell->type == ID($_DFF_N_)) {
						if (invert_sr) cell->type = ID($__DFFS_NN0_);
						else cell->type = ID($__DFFS_NP0_);
					} else {
						log_assert(cell->type == ID($_DFF_P_));
						if (invert_sr) cell->type = ID($__DFFS_PN0_);
						else cell->type = ID($__DFFS_PP0_);
					}
				}
				cell->setPort(ID(R), sr_sig);
				cell->setPort(ID(D), bit_d);
			}
		}
	}
} Dff2dffsPass;

PRIVATE_NAMESPACE_END
