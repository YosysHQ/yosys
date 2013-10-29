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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

struct SplitnetsWorker
{
	std::map<RTLIL::Wire*, std::vector<RTLIL::Wire*>> splitmap;

	void operator()(RTLIL::SigSpec &sig)
	{
		sig.expand();
		for (auto &c : sig.chunks)
			if (splitmap.count(c.wire) > 0) {
				c.wire = splitmap.at(c.wire).at(c.offset);
				c.offset = 0;
			}
		sig.optimize();
	}
};

struct SplitnetsPass : public Pass {
	SplitnetsPass() : Pass("splitnets", "split up multi-bit nets") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splitnets [options] [selection]\n");
		log("\n");
		log("This command splits multi-bit nets into single-bit nets.\n");
		log("\n");
		log("    -format char1[char2]\n");
		log("        the first char is inserted between the net name and the bit index, the\n");
		log("        second char is appended to the netname. e.g. -format () creates net\n");
		log("        names like 'mysignal(42)'. the default is '[]'.\n");
		log("\n");
		log("    -ports\n");
		log("        also split module ports. per default only internal signals are split.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_ports = false;
		std::string format = "[]";

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-format" && argidx+1 < args.size()) {
				format = args[++argidx];
				continue;
			}
			if (args[argidx] == "-ports") {
				flag_ports = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto &mod_it : design->modules)
		{
			RTLIL::Module *module = mod_it.second;
			if (!design->selected(module))
				continue;

			SplitnetsWorker worker;

			for (auto &w : module->wires) {
				RTLIL::Wire *wire = w.second;
				if (wire->width > 1 && (wire->port_id == 0 || flag_ports))
					worker.splitmap[wire] = std::vector<RTLIL::Wire*>();
			}

			for (auto &it : worker.splitmap)
				for (int i = 0; i < it.first->width; i++) {
					RTLIL::Wire *wire = new RTLIL::Wire;
					wire->port_id = it.first->port_id;
					wire->port_input = it.first->port_input;
					wire->port_output = it.first->port_output;
					wire->name = it.first->name;
					if (format.size() > 0)
						wire->name += format.substr(0, 1);
					wire->name += stringf("%d", i);
					if (format.size() > 0)
						wire->name += format.substr(1);
					while (module->count_id(wire->name) > 0)
						wire->name = wire->name + "_";
					module->add(wire);
					it.second.push_back(wire);
				}

			module->rewrite_sigspecs(worker);

			for (auto &it : worker.splitmap) {
				module->wires.erase(it.first->name);
				delete it.first;
			}

			module->fixup_ports();
		}
	}
} SplitnetsPass;
 
