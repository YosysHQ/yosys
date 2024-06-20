/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2024  Emily Schmidt <emily@yosyshq.com>
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
#include "kernel/functionalir.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

struct FunctionalTestGeneric : public Pass
{
	FunctionalTestGeneric() : Pass("test_generic", "test the generic compute graph") {}

    void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
    }

	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
        log_header(design, "Executing Test Generic.\n");

		size_t argidx = 1;
		extra_args(args, argidx, design);

		for (auto module : design->selected_modules()) {
            log("Dumping module `%s'.\n", module->name.c_str());
			auto fir = FunctionalIR::from_module(module);
			for(auto node : fir)
				std::cout << RTLIL::unescape_id(node.name()) << " = " << node.to_string([](auto n) { return RTLIL::unescape_id(n.name()); }) << "\n";
			for(auto [name, sort] : fir.outputs())
				std::cout << RTLIL::unescape_id(name) << " = " << RTLIL::unescape_id(fir.get_output_node(name).name()) << "\n";
			for(auto [name, sort] : fir.state())
				std::cout << RTLIL::unescape_id(name) << " = " << RTLIL::unescape_id(fir.get_state_next_node(name).name()) << "\n";
		}
	}
} FunctionalCxxBackend;

PRIVATE_NAMESPACE_END
