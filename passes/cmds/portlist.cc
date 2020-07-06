/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
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

struct PortlistPass : public Pass {
	PortlistPass() : Pass("portlist", "list (top-level) ports") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    portlist [options] [selection]\n");
		log("\n");
		log("This command lists all module ports found in the selected modules.\n");
		log("\n");
		log("If no selection is provided then it lists the ports on the top module.\n");
		log("\n");
		log("  -m\n");
		log("    print verilog blackbox module definitions instead of port lists\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool m_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-m") {
				m_mode = true;
				continue;
			}
			break;
		}

		bool first_module = true;

		auto handle_module = [&](RTLIL::Module *module) {
			vector<string> ports;
			if (first_module)
				first_module = false;
			else
				log("\n");
			for (auto port : module->ports) {
				auto *w = module->wire(port);
				ports.push_back(stringf("%s [%d:%d] %s", w->port_input ? w->port_output ? "inout" : "input" : "output",
						w->upto ? w->start_offset : w->start_offset + w->width - 1,
						w->upto ? w->start_offset + w->width - 1 : w->start_offset,
						log_id(w)));
			}
			log("module %s%s\n", log_id(module), m_mode ? " (" : "");
			for (int i = 0; i < GetSize(ports); i++)
				log("%s%s\n", ports[i].c_str(), m_mode && i+1 < GetSize(ports) ? "," : "");
			if (m_mode)
				log(");\nendmodule\n");
		};

		if (argidx == args.size())
		{
			auto *top = design->top_module();
			if (top == nullptr)
				log_cmd_error("Can't find top module in current design!\n");
			handle_module(top);
		}
		else
		{
			extra_args(args, argidx, design);
			for (auto module : design->selected_modules())
				handle_module(module);
		}
	}
} PortlistPass;

PRIVATE_NAMESPACE_END
