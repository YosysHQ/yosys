/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2019  Marcin Kościelnicki <mwk@0x04.net>
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

void split_portname_pair(std::string &port1, std::string &port2)
{
	size_t pos = port1.find_first_of(':');
	if (pos != std::string::npos) {
		port2 = port1.substr(pos+1);
		port1 = port1.substr(0, pos);
	}
}

struct ClkbufmapPass : public Pass {
	ClkbufmapPass() : Pass("clkbufmap", "insert global buffers on clock networks") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    clkbufmap [options] [selection]\n");
		log("\n");
		log("Inserts global buffers between nets connected to clock inputs and their drivers.\n");
		log("\n");
		log("In the absence of any selection, all wires without the 'clkbuf_inhibit'\n");
		log("attribute will be considered for global buffer insertion.\n");
		log("Alternatively, to consider all wires without the 'buffer_type' attribute set to\n");
		log("'none' or 'bufr' one would specify:\n");
		log("  'w:* a:buffer_type=none a:buffer_type=bufr %%u %%d'\n");
		log("as the selection.\n");
		log("\n");
		log("    -buf <celltype> <portname_out>:<portname_in>\n");
		log("        Specifies the cell type to use for the global buffers\n");
		log("        and its port names.  The first port will be connected to\n");
		log("        the clock network sinks, and the second will be connected\n");
		log("        to the actual clock source.  This option is required.\n");
		log("\n");
		log("    -inpad <celltype> <portname_out>:<portname_in>\n");
		log("        If specified, a PAD cell of the given type is inserted on\n");
		log("        clock nets that are also top module's inputs (in addition\n");
		log("        to the global buffer).\n");
		log("\n");
	}

	void module_queue(Design *design, Module *module, std::vector<Module *> &modules_sorted, pool<Module *> &modules_processed) {
		if (modules_processed.count(module))
			return;
		for (auto cell : module->cells()) {
			Module *submodule = design->module(cell->type);
			if (!submodule)
				continue;
			module_queue(design, submodule, modules_sorted, modules_processed);
		}
		modules_sorted.push_back(module);
		modules_processed.insert(module);
	}

	void execute(std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		log_header(design, "Executing CLKBUFMAP pass (inserting global clock buffers).\n");

		std::string buf_celltype, buf_portname, buf_portname2;
		std::string inpad_celltype, inpad_portname, inpad_portname2;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-buf" && argidx+2 < args.size()) {
				buf_celltype = args[++argidx];
				buf_portname = args[++argidx];
				split_portname_pair(buf_portname, buf_portname2);
				continue;
			}
			if (arg == "-inpad" && argidx+2 < args.size()) {
				inpad_celltype = args[++argidx];
				inpad_portname = args[++argidx];
				split_portname_pair(inpad_portname, inpad_portname2);
				continue;
			}
			break;
		}

		bool select = false;
		if (argidx < args.size()) {
			if (args[argidx].compare(0, 1, "-") != 0)
				select = true;
			extra_args(args, argidx, design);
		}

		if (buf_celltype.empty())
			log_error("The -buf option is required.\n");

		// Cell type, port name, bit index.
		pool<pair<IdString, pair<IdString, int>>> sink_ports;
		pool<pair<IdString, pair<IdString, int>>> buf_ports;
		dict<pair<IdString, pair<IdString, int>>, pair<IdString, int>> inv_ports_out;
		dict<pair<IdString, pair<IdString, int>>, pair<IdString, int>> inv_ports_in;

		// Process submodules before module using them.
		std::vector<Module *> modules_sorted;
		pool<Module *> modules_processed;
		for (auto module : design->selected_modules())
			module_queue(design, module, modules_sorted, modules_processed);

		for (auto module : modules_sorted)
		{
			if (module->get_blackbox_attribute()) {
				for (auto port : module->ports) {
					auto wire = module->wire(port);
					if (wire->get_bool_attribute("\\clkbuf_driver"))
						for (int i = 0; i < GetSize(wire); i++)
							buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					if (wire->get_bool_attribute("\\clkbuf_sink"))
						for (int i = 0; i < GetSize(wire); i++)
							sink_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					auto it = wire->attributes.find("\\clkbuf_inv");
					if (it != wire->attributes.end()) {
						IdString in_name = RTLIL::escape_id(it->second.decode_string());
						for (int i = 0; i < GetSize(wire); i++) {
							inv_ports_out[make_pair(module->name, make_pair(wire->name, i))] = make_pair(in_name, i);
							inv_ports_in[make_pair(module->name, make_pair(in_name, i))] = make_pair(wire->name, i);
						}
					}
				}
				continue;
			}
			pool<SigBit> sink_wire_bits;
			pool<SigBit> buf_wire_bits;
			pool<SigBit> driven_wire_bits;
			SigMap sigmap(module);
			// bit -> (buffer, buffer's input)
			dict<SigBit, pair<Cell *, Wire *>> buffered_bits;

			// First, collect nets that could use a clock buffer.
			for (auto cell : module->cells())
			for (auto port : cell->connections())
			for (int i = 0; i < port.second.size(); i++)
				if (sink_ports.count(make_pair(cell->type, make_pair(port.first, i))))
					sink_wire_bits.insert(sigmap(port.second[i]));

			// Second, collect ones that already have a clock buffer.
			for (auto cell : module->cells())
			for (auto port : cell->connections())
			for (int i = 0; i < port.second.size(); i++)
				if (buf_ports.count(make_pair(cell->type, make_pair(port.first, i))))
					buf_wire_bits.insert(sigmap(port.second[i]));

			// Third, propagate tags through inverters.
			bool retry = true;
			while (retry) {
				retry = false;
				for (auto cell : module->cells())
				for (auto port : cell->connections())
				for (int i = 0; i < port.second.size(); i++) {
					auto it = inv_ports_out.find(make_pair(cell->type, make_pair(port.first, i)));
					auto bit = sigmap(port.second[i]);
					// If output of an inverter is connected to a sink, mark it as buffered,
					// and request a buffer on the inverter's input instead.
					if (it != inv_ports_out.end() && !buf_wire_bits.count(bit) && sink_wire_bits.count(bit)) {
						buf_wire_bits.insert(bit);
						auto other_bit = sigmap(cell->getPort(it->second.first)[it->second.second]);
						sink_wire_bits.insert(other_bit);
						retry = true;
					}
					// If input of an inverter is marked as already-buffered,
					// mark its output already-buffered as well.
					auto it2 = inv_ports_in.find(make_pair(cell->type, make_pair(port.first, i)));
					if (it2 != inv_ports_in.end() && buf_wire_bits.count(bit)) {
						auto other_bit = sigmap(cell->getPort(it2->second.first)[it2->second.second]);
						if (!buf_wire_bits.count(other_bit)) {
							buf_wire_bits.insert(other_bit);
							retry = true;
						}
					}

				}
			};

			// Collect all driven bits.
			for (auto cell : module->cells())
			for (auto port : cell->connections())
				if (cell->output(port.first))
					for (int i = 0; i < port.second.size(); i++)
						driven_wire_bits.insert(port.second[i]);

			// Insert buffers.
			std::vector<pair<Wire *, Wire *>> input_queue;
			// Copy current wire list, as we will be adding new ones during iteration.
			std::vector<Wire *> wires(module->wires());
			for (auto wire : wires)
			{
				// Should not happen.
				if (wire->port_input && wire->port_output)
					continue;
				bool process_wire = module->selected(wire);
				if (!select && wire->get_bool_attribute("\\clkbuf_inhibit"))
					process_wire = false;
				if (!process_wire) {
					// This wire is supposed to be bypassed, so make sure we don't buffer it in
					// some buffer higher up in the hierarchy.
					if (wire->port_output)
						for (int i = 0; i < GetSize(wire); i++)
							buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					continue;
				}

				pool<int> input_bits;

				for (int i = 0; i < GetSize(wire); i++)
				{
					SigBit wire_bit(wire, i);
					SigBit mapped_wire_bit = sigmap(wire_bit);
					if (buf_wire_bits.count(mapped_wire_bit)) {
						// Already buffered downstream.  If this is an output, mark it.
						if (wire->port_output)
							buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					} else if (!sink_wire_bits.count(mapped_wire_bit)) {
						// Nothing to do.
					} else if (driven_wire_bits.count(wire_bit) || (wire->port_input && module->get_bool_attribute("\\top"))) {
						// Clock network not yet buffered, driven by one of
						// our cells or a top-level input -- buffer it.

						log("Inserting %s on %s.%s[%d].\n", buf_celltype.c_str(), log_id(module), log_id(wire), i);
						RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(buf_celltype));
						Wire *iwire = module->addWire(NEW_ID);
						cell->setPort(RTLIL::escape_id(buf_portname), mapped_wire_bit);
						cell->setPort(RTLIL::escape_id(buf_portname2), iwire);
						if (wire->port_input && !inpad_celltype.empty() && module->get_bool_attribute("\\top")) {
							log("Inserting %s on %s.%s[%d].\n", inpad_celltype.c_str(), log_id(module), log_id(wire), i);
							RTLIL::Cell *cell2 = module->addCell(NEW_ID, RTLIL::escape_id(inpad_celltype));
							cell2->setPort(RTLIL::escape_id(inpad_portname), iwire);
							iwire = module->addWire(NEW_ID);
							cell2->setPort(RTLIL::escape_id(inpad_portname2), iwire);
						}
						buffered_bits[mapped_wire_bit] = make_pair(cell, iwire);

						if (wire->port_input) {
							input_bits.insert(i);
						}
					} else if (wire->port_input) {
						// A clock input in a submodule -- mark it, let higher level
						// worry about it.
						if (wire->port_input)
							sink_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					}
				}
				if (!input_bits.empty()) {
					// This is an input port and some buffers were inserted -- we need
					// to create a new input wire and transfer attributes.
					Wire *new_wire = module->addWire(NEW_ID, wire);

					for (int i = 0; i < wire->width; i++) {
						SigBit wire_bit(wire, i);
						SigBit mapped_wire_bit = sigmap(wire_bit);
						auto it = buffered_bits.find(mapped_wire_bit);
						if (it != buffered_bits.end()) {

							module->connect(it->second.second, SigSpec(new_wire, i));
						} else {
							module->connect(SigSpec(wire, i), SigSpec(new_wire, i));
						}
					}
					input_queue.push_back(make_pair(wire, new_wire));
				}
			}

			// Mark any newly-buffered output ports as such.
			for (auto wire : module->selected_wires()) {
				if (wire->port_input || !wire->port_output)
					continue;
				for (int i = 0; i < GetSize(wire); i++)
				{
					SigBit wire_bit(wire, i);
					SigBit mapped_wire_bit = sigmap(wire_bit);
					if (buffered_bits.count(mapped_wire_bit))
						buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
				}
			}

			// Reconnect the drivers to buffer inputs.
			for (auto cell : module->cells())
			for (auto port : cell->connections()) {
				if (!cell->output(port.first))
					continue;
				SigSpec sig = port.second;
				bool newsig = false;
				for (auto &bit : sig) {
					const auto it = buffered_bits.find(sigmap(bit));
					if (it == buffered_bits.end())
						continue;
					// Avoid substituting buffer's own output pin.
					if (cell == it->second.first)
						continue;
					bit = it->second.second;
					newsig = true;
				}
				if (newsig)
					cell->setPort(port.first, sig);
			}

			// This has to be done last, to avoid upsetting sigmap before the port reconnections.
			for (auto &it : input_queue) {
				Wire *wire = it.first;
				Wire *new_wire = it.second;
				module->swap_names(new_wire, wire);
				wire->attributes.clear();
				wire->port_id = 0;
				wire->port_input = false;
				wire->port_output = false;
			}

			module->fixup_ports();
		}
	}
} ClkbufmapPass;

PRIVATE_NAMESPACE_END
