/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2020  Alberto Gonzalez <boqwxp@airmail.cc>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct PrintAttrsPass : public Pass {
	PrintAttrsPass() : Pass("printattrs", "print attributes of selected objects") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    printattrs [selection]\n");
		log("\n");
		log("Print all attributes of the selected objects.\n");
		log("\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		size_t argidx = 1;
		extra_args(args, argidx, design);

		unsigned int indent = 0;
		for (auto mod : design->selected_modules())
		{

			if (design->selected_whole_module(mod)) {
				log("%s%s\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(mod->name));
				indent += 2;
				for (auto &it : mod->attributes)
					log("%s(* %s=\"%s\" %s *)\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(it.first), it.second.decode_string().c_str(), it.second.as_string().c_str());
			}

			for (auto cell : mod->selected_cells()) {
				log("%s%s\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(cell->name));
				indent += 2;
				for (auto &it : cell->attributes) {
					log("%s(* %s=\"%s\" %s *)\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(it.first), it.second.decode_string().c_str(), it.second.as_string().c_str());
				}
				indent -= 2;
			}

			for (auto wire : mod->selected_wires()) {
				log("%s%s\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(wire->name));
				indent += 2;
				for (auto &it : wire->attributes) {
					log("%s(* %s=\"%s\" %s *)\n", stringf(stringf("%%%ds", indent).c_str(), " ").c_str(), log_id(it.first), it.second.decode_string().c_str(), it.second.as_string().c_str());
				}
				indent -= 2;
			}

			if (design->selected_whole_module(mod))
				indent -= 2;
		}

		log("\n");
	}
} PrintAttrsPass;

PRIVATE_NAMESPACE_END
