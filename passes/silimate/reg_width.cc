/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
 *                2026  Stan Lee          <stan@silimate.com>
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
 #include <regex>
 
 USING_YOSYS_NAMESPACE
 PRIVATE_NAMESPACE_BEGIN
 
 struct RegWidthPass : public Pass {
	 RegWidthPass() : Pass("reg_width", "annotates multi-bit registers with their width") { }
	 void help() override
	 {
		 //   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		 log("\n");
		 log("    reg_width\n");
		 log("\n");
	 }
	 void execute(std::vector<std::string> args, RTLIL::Design *design) override
	 {
		 log_header(design, "Executing reg_width pass\n");
 
		 size_t argidx;
		 for (argidx = 1; argidx < args.size(); argidx++) {
			 // No options currently. When adding in the future make sure to update docstring with [options]
			 break;
		 }
		 extra_args(args, argidx, design);
 
			// Data structure used to keep track of multi-bit registers.
			// Relevant for correct register annotation.
			for (auto module : design->selected_modules()) {
				log("Processing module %s\n", module->name.c_str());
				for (auto cell : module->selected_cells()) {
					if (cell->name.ends_with("_reg")) {
						std::string width = std::to_string(cell->getParam(ID::WIDTH).as_int());
						if (width != "1") { // only care about multi-bit registers
							cell->set_string_attribute("$ORIG_REG_WIDTH", width);
							log("Annotating register %s with width %s\n", cell->name.c_str(), width);
						}
					}
				}
			}

		 log_flush();
	 }
 } RegWidthPass;
 
 PRIVATE_NAMESPACE_END
 