/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2023  N. Engelhardt <nak@yosyshq.com>
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

#include "kernel/log.h"
#include "kernel/register.h"
#include "kernel/rtlil.h"
#include "kernel/sigtools.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

// ============================================================================


struct QlBramTypesPass : public Pass {
	
	QlBramTypesPass() : Pass("ql_bram_types", "Change TDP36K type to subtypes") {}

	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    ql_bram_types [selection]\n");
		log("\n");
		log("    This pass changes the type of TDP36K cells to different types based on the\n");
		log("    configuration of the cell.\n");
		log("\n");
	}

	int width_for_mode(int mode){
		// 1: mode = 3'b101;
		// 2: mode = 3'b110;
		// 4: mode = 3'b100;
		// 8,9: mode = 3'b001;
		// 16, 18: mode = 3'b010;
		// 32, 36: mode = 3'b011;
		switch (mode)
		{
		case 1:
			return 9;
		case 2:
			return 18;
		case 3:
			return 36;
		case 4:
			return 4;
		case 5:
			return 1;
		case 6:
			return 2;
		default:
			log_error("Invalid mode: %x", mode);
		}
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing QL_BRAM_TYPES pass.\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (RTLIL::Module* module : design->selected_modules())
			for (RTLIL::Cell* cell: module->selected_cells())
			{
				if (cell->type != ID(TDP36K) || !cell->hasParam(ID(MODE_BITS)))
					continue;
				
				RTLIL::Const mode_bits = cell->getParam(ID(MODE_BITS));

				bool split = mode_bits.extract(80).as_bool();

				bool FMODE1_i = mode_bits.extract(13).as_bool();
				bool FMODE2_i = mode_bits.extract(54).as_bool();
				if (FMODE1_i != FMODE2_i) {
					log_debug("Can't change type of mixed use TDP36K block: FMODE1_i = %s, FMODE2_i = %s\n", FMODE1_i ? "true" : "false", FMODE2_i ? "true" : "false");
					continue;
				}
				bool is_fifo = FMODE1_i;

				bool SYNC_FIFO1_i = mode_bits.extract(0).as_bool();
				bool SYNC_FIFO2_i = mode_bits.extract(41).as_bool();
				if (SYNC_FIFO1_i != SYNC_FIFO2_i) {
					log_debug("Can't change type of mixed use TDP36K block: SYNC_FIFO1_i = %s, SYNC_FIFO2_i = %s\n", SYNC_FIFO1_i ? "true" : "false", SYNC_FIFO2_i ? "true" : "false");
					continue;
				}
				bool sync_fifo = SYNC_FIFO1_i;

				int RMODE_A1_i = mode_bits.extract(1, 3).as_int();
				int RMODE_B1_i = mode_bits.extract(4, 3).as_int();
				int WMODE_A1_i = mode_bits.extract(7, 3).as_int();
				int WMODE_B1_i = mode_bits.extract(10, 3).as_int();

				int RMODE_A2_i = mode_bits.extract(42, 3).as_int();
				int RMODE_B2_i = mode_bits.extract(45, 3).as_int();
				int WMODE_A2_i = mode_bits.extract(48, 3).as_int();
				int WMODE_B2_i = mode_bits.extract(51, 3).as_int();

				// TODO: should these be a warning or an error?
				if (RMODE_A1_i != WMODE_A1_i) {
					log_warning("Can't change type of misconfigured TDP36K block: Port A1 configured with read width = %d different from write width = %d\n", width_for_mode(RMODE_A1_i), width_for_mode(WMODE_A1_i));
					continue;
				}
				if (RMODE_B1_i != WMODE_B1_i) {
					log_warning("Can't change type of misconfigured TDP36K block: Port B1 configured with read width = %d different from write width = %d\n", width_for_mode(RMODE_B1_i), width_for_mode(WMODE_B1_i));
					continue;
				}
				if (RMODE_A2_i != WMODE_A2_i) {
					log_warning("Can't change type of misconfigured TDP36K block: Port A2 configured with read width = %d different from write width = %d\n", width_for_mode(RMODE_A2_i), width_for_mode(WMODE_A2_i));
					continue;
				}
				if (RMODE_B2_i != WMODE_B2_i) {
					log_warning("Can't change type of misconfigured TDP36K block: Port B2 configured with read width = %d different from write width = %d\n", width_for_mode(RMODE_B2_i), width_for_mode(WMODE_B2_i));
					continue;
				}

				// TODO: For nonsplit blocks, should RMODE_A1_i == RMODE_A2_i etc be checked/enforced?

				std::string type = "TDP36K";
				if (is_fifo) {
					type += "_FIFO_";
					if (sync_fifo)
						type += "SYNC_";
					else
						type += "ASYNC_";
				} else 
					type += "_BRAM_";

				if (split) {
					type += stringf("A1_X%d_", width_for_mode(RMODE_A1_i));
					type += stringf("B1_X%d_", width_for_mode(RMODE_B1_i));
					type += stringf("A2_X%d_", width_for_mode(RMODE_A2_i));
					type += stringf("B2_X%d_", width_for_mode(RMODE_B2_i));
					type += "split";
				} else {
					type += stringf("A_X%d_", width_for_mode(RMODE_A1_i));
					type += stringf("B_X%d_", width_for_mode(RMODE_B1_i));
					type += "nonsplit";
				}

				cell->type = RTLIL::escape_id(type);
				log_debug("Changed type of memory cell %s to %s\n", log_id(cell->name), log_id(cell->type));
			}
	}


} QlBramMergePass;

PRIVATE_NAMESPACE_END