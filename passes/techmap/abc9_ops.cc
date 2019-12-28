/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung <eddie@fpgeh.com>
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

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

void break_scc(RTLIL::Module *module)
{
	// For every unique SCC found, (arbitrarily) find the first
	//   cell in the component, and convert all wires driven by
	//   its output ports into a new PO, and drive its previous
	//   sinks with a new PI
	pool<RTLIL::Const> ids_seen;
	for (auto cell : module->selected_cells()) {
		auto it = cell->attributes.find(ID(abc9_scc_id));
		if (it == cell->attributes.end())
			continue;
		auto r = ids_seen.insert(it->second);
		cell->attributes.erase(it);
		if (!r.second)
			continue;
		for (auto &c : cell->connections_) {
			if (c.second.is_fully_const()) continue;
			if (cell->output(c.first)) {
				SigBit b = c.second.as_bit();
				Wire *w = b.wire;
				if (w->port_input) {
					// In this case, hopefully the loop break has been already created
					// Get the non-prefixed wire
					Wire *wo = module->wire(stringf("%s.abco", b.wire->name.c_str()));
					log_assert(wo != nullptr);
					log_assert(wo->port_output);
					log_assert(b.offset < GetSize(wo));
					c.second = RTLIL::SigBit(wo, b.offset);
				}
				else {
					// Create a new output/input loop break
					w->port_input = true;
					w = module->wire(stringf("%s.abco", w->name.c_str()));
					if (!w) {
						w = module->addWire(stringf("%s.abco", b.wire->name.c_str()), GetSize(b.wire));
						w->port_output = true;
					}
					else {
						log_assert(w->port_input);
						log_assert(b.offset < GetSize(w));
					}
					w->set_bool_attribute(ID(abc9_scc_break));
					c.second = RTLIL::SigBit(w, b.offset);
				}
			}
		}
	}

	module->fixup_ports();
}

void unbreak_scc(RTLIL::Module *module) {
	// Now 'unexpose' those wires by undoing
	// the expose operation -- remove them from PO/PI
	// and re-connecting them back together
	for (auto wire : module->wires()) {
		auto it = wire->attributes.find(ID(abc9_scc_break));
		if (it != wire->attributes.end()) {
			wire->attributes.erase(it);
			log_assert(wire->port_output);
			wire->port_output = false;
			std::string name = wire->name.str();
			RTLIL::Wire *i_wire = module->wire(name.substr(0, GetSize(name) - 5));
			log_assert(i_wire);
			log_assert(i_wire->port_input);
			i_wire->port_input = false;
			module->connect(i_wire, wire);
		}
	}
	module->fixup_ports();
}

struct Abc9PrepPass : public Pass {
	Abc9PrepPass() : Pass("abc9_ops", "helper functions for ABC9") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc9_ops [options] [selection]\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing ABC9_OPS pass (helper functions for ABC9).\n");
		log_push();

		bool break_scc_mode = false;
		bool unbreak_scc_mode = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-break_scc") {
				break_scc_mode = true;
				continue;
			}
			if (arg == "-unbreak_scc") {
				unbreak_scc_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (break_scc_mode)
				break_scc(mod);
			if (unbreak_scc_mode)
				unbreak_scc(mod);
		}
	}
} Abc9PrepPass;

PRIVATE_NAMESPACE_END
