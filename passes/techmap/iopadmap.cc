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

void split_portname_pair(std::string &port1, std::string &port2)
{
	size_t pos = port1.find_first_of(':');
	if (pos != std::string::npos) {
		port2 = port1.substr(pos+1);
		port1 = port1.substr(0, pos);
	}
}

struct IopadmapPass : public Pass {
	IopadmapPass() : Pass("iopadmap", "technology mapping of i/o pads (or buffers)") { }
	void help() YS_OVERRIDE
	{
		log("\n");
		log("    iopadmap [options] [selection]\n");
		log("\n");
		log("Map module inputs/outputs to PAD cells from a library. This pass\n");
		log("can only map to very simple PAD cells. Use 'techmap' to further map\n");
		log("the resulting cells to more sophisticated PAD cells.\n");
		log("\n");
		log("    -inpad <celltype> <portname>[:<portname>]\n");
		log("        Map module input ports to the given cell type with the\n");
		log("        given output port name. if a 2nd portname is given, the\n");
		log("        signal is passed through the pad call, using the 2nd\n");
		log("        portname as the port facing the module port.\n");
		log("\n");
		log("    -outpad <celltype> <portname>[:<portname>]\n");
		log("    -inoutpad <celltype> <portname>[:<portname>]\n");
		log("        Similar to -inpad, but for output and inout ports.\n");
		log("\n");
		log("    -toutpad <celltype> <portname>:<portname>[:<portname>]\n");
		log("        Merges $_TBUF_ cells into the output pad cell. This takes precedence\n");
		log("        over the other -outpad cell. The first portname is the enable input\n");
		log("        of the tristate driver.\n");
		log("\n");
		log("    -tinoutpad <celltype> <portname>:<portname>:<portname>[:<portname>]\n");
		log("        Merges $_TBUF_ cells into the inout pad cell. This takes precedence\n");
		log("        over the other -inoutpad cell. The first portname is the enable input\n");
		log("        of the tristate driver and the 2nd portname is the internal output\n");
		log("        buffering the external signal.\n");
		log("\n");
		log("    -ignore <celltype> <portname>[:<portname>]*\n");
		log("        Skips mapping inputs/outputs that are already connected to given\n");
		log("        ports of the given cell.  Can be used multiple times.  This is in\n");
		log("        addition to the cells specified as mapping targets.\n");
		log("\n");
		log("    -widthparam <param_name>\n");
		log("        Use the specified parameter name to set the port width.\n");
		log("\n");
		log("    -nameparam <param_name>\n");
		log("        Use the specified parameter to set the port name.\n");
		log("\n");
		log("    -bits\n");
		log("        create individual bit-wide buffers even for ports that\n");
		log("        are wider. (the default behavior is to create word-wide\n");
		log("        buffers using -widthparam to set the word size on the cell.)\n");
		log("\n");
		log("Tristate PADS (-toutpad, -tinoutpad) always operate in -bits mode.\n");
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
		log_header(design, "Executing IOPADMAP pass (mapping inputs/outputs to IO-PAD cells).\n");

		std::string inpad_celltype, inpad_portname_o, inpad_portname_pad;
		std::string outpad_celltype, outpad_portname_i, outpad_portname_pad;
		std::string inoutpad_celltype, inoutpad_portname_io, inoutpad_portname_pad;
		std::string toutpad_celltype, toutpad_portname_oe, toutpad_portname_i, toutpad_portname_pad;
		std::string tinoutpad_celltype, tinoutpad_portname_oe, tinoutpad_portname_o, tinoutpad_portname_i, tinoutpad_portname_pad;
		std::string widthparam, nameparam;
		pool<pair<IdString, IdString>> ignore;
		bool flag_bits = false;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-inpad" && argidx+2 < args.size()) {
				inpad_celltype = args[++argidx];
				inpad_portname_o = args[++argidx];
				split_portname_pair(inpad_portname_o, inpad_portname_pad);
				continue;
			}
			if (arg == "-outpad" && argidx+2 < args.size()) {
				outpad_celltype = args[++argidx];
				outpad_portname_i = args[++argidx];
				split_portname_pair(outpad_portname_i, outpad_portname_pad);
				continue;
			}
			if (arg == "-inoutpad" && argidx+2 < args.size()) {
				inoutpad_celltype = args[++argidx];
				inoutpad_portname_io = args[++argidx];
				split_portname_pair(inoutpad_portname_io, inoutpad_portname_pad);
				continue;
			}
			if (arg == "-toutpad" && argidx+2 < args.size()) {
				toutpad_celltype = args[++argidx];
				toutpad_portname_oe = args[++argidx];
				split_portname_pair(toutpad_portname_oe, toutpad_portname_i);
				split_portname_pair(toutpad_portname_i, toutpad_portname_pad);
				continue;
			}
			if (arg == "-tinoutpad" && argidx+2 < args.size()) {
				tinoutpad_celltype = args[++argidx];
				tinoutpad_portname_oe = args[++argidx];
				split_portname_pair(tinoutpad_portname_oe, tinoutpad_portname_o);
				split_portname_pair(tinoutpad_portname_o, tinoutpad_portname_i);
				split_portname_pair(tinoutpad_portname_i, tinoutpad_portname_pad);
				continue;
			}
			if (arg == "-ignore" && argidx+2 < args.size()) {
				std::string ignore_celltype = args[++argidx];
				std::string ignore_portname = args[++argidx];
				std::string ignore_portname2;
				while (!ignore_portname.empty()) {
					split_portname_pair(ignore_portname, ignore_portname2);
					ignore.insert(make_pair(RTLIL::escape_id(ignore_celltype), RTLIL::escape_id(ignore_portname)));

					ignore_portname = ignore_portname2;
				}
				continue;
			}
			if (arg == "-widthparam" && argidx+1 < args.size()) {
				widthparam = args[++argidx];
				continue;
			}
			if (arg == "-nameparam" && argidx+1 < args.size()) {
				nameparam = args[++argidx];
				continue;
			}
			if (arg == "-bits") {
				flag_bits = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (!inpad_portname_pad.empty())
			ignore.insert(make_pair(RTLIL::escape_id(inpad_celltype), RTLIL::escape_id(inpad_portname_pad)));
		if (!outpad_portname_pad.empty())
			ignore.insert(make_pair(RTLIL::escape_id(outpad_celltype), RTLIL::escape_id(outpad_portname_pad)));
		if (!inoutpad_portname_pad.empty())
			ignore.insert(make_pair(RTLIL::escape_id(inoutpad_celltype), RTLIL::escape_id(inoutpad_portname_pad)));
		if (!toutpad_portname_pad.empty())
			ignore.insert(make_pair(RTLIL::escape_id(toutpad_celltype), RTLIL::escape_id(toutpad_portname_pad)));
		if (!tinoutpad_portname_pad.empty())
			ignore.insert(make_pair(RTLIL::escape_id(tinoutpad_celltype), RTLIL::escape_id(tinoutpad_portname_pad)));

		// Recursively collect list of (module, port, bit) triples that already have buffers.

		pool<pair<IdString, pair<IdString, int>>> buf_ports;

		// Process submodules before module using them.
		std::vector<Module *> modules_sorted;
		pool<Module *> modules_processed;
		for (auto module : design->selected_modules())
			module_queue(design, module, modules_sorted, modules_processed);

		for (auto module : modules_sorted)
		{
			pool<SigBit> buf_bits;
			SigMap sigmap(module);

			// Collect explicitly-marked already-buffered SigBits.
			for (auto wire : module->wires())
				if (wire->get_bool_attribute("\\iopad_external_pin") || ignore.count(make_pair(module->name, wire->name)))
					for (int i = 0; i < GetSize(wire); i++)
						buf_bits.insert(sigmap(SigBit(wire, i)));

			// Collect SigBits connected to already-buffered ports.
			for (auto cell : module->cells())
			for (auto port : cell->connections())
			for (int i = 0; i < port.second.size(); i++)
				if (buf_ports.count(make_pair(cell->type, make_pair(port.first, i))))
					buf_bits.insert(sigmap(port.second[i]));

			// Now fill buf_ports.
			for (auto wire : module->wires())
				if (wire->port_input || wire->port_output)
					for (int i = 0; i < GetSize(wire); i++)
						if (buf_bits.count(sigmap(SigBit(wire, i)))) {
							buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
							log("Marking already mapped port: %s.%s[%d].\n", log_id(module), log_id(wire), i);
						}
		}

		// Now do the actual buffer insertion.

		for (auto module : design->selected_modules())
		{
			dict<Wire *, dict<int, pair<Cell *, IdString>>> rewrite_bits;

			if (!toutpad_celltype.empty() || !tinoutpad_celltype.empty())
			{
				dict<SigBit, Cell *> tbuf_bits;
				pool<SigBit> driven_bits;

				// Gather tristate buffers and always-on drivers.
				for (auto cell : module->cells())
					if (cell->type == ID($_TBUF_)) {
						SigBit bit = cell->getPort(ID::Y).as_bit();
						tbuf_bits[bit] = cell;
					} else {
						for (auto port : cell->connections())
							if (!cell->known() || cell->output(port.first))
								for (auto bit : port.second)
									driven_bits.insert(bit);
					}

				// If a wire is a target of an assignment, it is driven, unless the source is 'z.
				for (auto &conn : module->connections())
					for (int i = 0; i < GetSize(conn.first); i++) {
						SigBit dstbit = conn.first[i];
						SigBit srcbit = conn.second[i];
						if (!srcbit.wire && srcbit.data == State::Sz)
							continue;
						driven_bits.insert(dstbit);
					}

				for (auto wire : module->selected_wires())
				{
					if (!wire->port_output)
						continue;

					// Don't handle inout ports if we have no suitable buffer type.
					if (wire->port_input && tinoutpad_celltype.empty())
						continue;

					// likewise for output ports.
					if (!wire->port_input && toutpad_celltype.empty())
						continue;

					for (int i = 0; i < GetSize(wire); i++)
					{
						SigBit wire_bit(wire, i);
						Cell *tbuf_cell = nullptr;

						if (buf_ports.count(make_pair(module->name, make_pair(wire->name, i))))
							continue;

						if (tbuf_bits.count(wire_bit))
							tbuf_cell = tbuf_bits.at(wire_bit);

						SigBit en_sig;
						SigBit data_sig;
						bool is_driven = driven_bits.count(wire_bit);

						if (tbuf_cell != nullptr) {
							// Found a tristate buffer — use it.
							en_sig = tbuf_cell->getPort(ID(E)).as_bit();
							data_sig = tbuf_cell->getPort(ID::A).as_bit();
						} else if (is_driven) {
							// No tristate buffer, but an always-on driver is present.
							// If this is an inout port, we're creating a tinoutpad
							// anyway, just with a constant 1 as enable.
							if (!wire->port_input)
								continue;
							en_sig = SigBit(State::S1);
							data_sig = wire_bit;
						} else {
							// No driver on a wire.  Create a tristate pad with always-0
							// enable.
							en_sig = SigBit(State::S0);
							data_sig = SigBit(State::Sx);
						}

						if (wire->port_input)
						{
							log("Mapping port %s.%s[%d] using %s.\n", log_id(module), log_id(wire), i, tinoutpad_celltype.c_str());

							Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(tinoutpad_celltype));

							cell->setPort(RTLIL::escape_id(tinoutpad_portname_oe), en_sig);
							cell->attributes[ID::keep] = RTLIL::Const(1);

							if (tbuf_cell) {
								module->remove(tbuf_cell);
								cell->setPort(RTLIL::escape_id(tinoutpad_portname_o), wire_bit);
								cell->setPort(RTLIL::escape_id(tinoutpad_portname_i), data_sig);
							} else if (is_driven) {
								cell->setPort(RTLIL::escape_id(tinoutpad_portname_i), wire_bit);
							} else {
								cell->setPort(RTLIL::escape_id(tinoutpad_portname_o), wire_bit);
								cell->setPort(RTLIL::escape_id(tinoutpad_portname_i), data_sig);
							}
							if (!tinoutpad_portname_pad.empty())
								rewrite_bits[wire][i] = make_pair(cell, RTLIL::escape_id(tinoutpad_portname_pad));
						} else {
							log("Mapping port %s.%s[%d] using %s.\n", log_id(module), log_id(wire), i, toutpad_celltype.c_str());

							Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(toutpad_celltype));

							cell->setPort(RTLIL::escape_id(toutpad_portname_oe), en_sig);
							cell->setPort(RTLIL::escape_id(toutpad_portname_i), data_sig);
							cell->attributes[ID::keep] = RTLIL::Const(1);

							if (tbuf_cell) {
								module->remove(tbuf_cell);
								module->connect(wire_bit, data_sig);
							}
							if (!toutpad_portname_pad.empty())
								rewrite_bits[wire][i] = make_pair(cell, RTLIL::escape_id(toutpad_portname_pad));
						}
						buf_ports.insert(make_pair(module->name, make_pair(wire->name, i)));
					}
				}
			}

			for (auto wire : module->selected_wires())
			{
				if (!wire->port_id)
					continue;

				std::string celltype, portname_int, portname_pad;
				pool<int> skip_bit_indices;

				for (int i = 0; i < GetSize(wire); i++)
					if (buf_ports.count(make_pair(module->name, make_pair(wire->name, i))))
						skip_bit_indices.insert(i);

				if (GetSize(wire) == GetSize(skip_bit_indices))
					continue;

				if (wire->port_input && !wire->port_output) {
					if (inpad_celltype.empty()) {
						log("Don't map input port %s.%s: Missing option -inpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = inpad_celltype;
					portname_int = inpad_portname_o;
					portname_pad = inpad_portname_pad;
				} else
				if (!wire->port_input && wire->port_output) {
					if (outpad_celltype.empty()) {
						log("Don't map output port %s.%s: Missing option -outpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = outpad_celltype;
					portname_int = outpad_portname_i;
					portname_pad = outpad_portname_pad;
				} else
				if (wire->port_input && wire->port_output) {
					if (inoutpad_celltype.empty()) {
						log("Don't map inout port %s.%s: Missing option -inoutpad.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
						continue;
					}
					celltype = inoutpad_celltype;
					portname_int = inoutpad_portname_io;
					portname_pad = inoutpad_portname_pad;
				} else
					log_abort();

				if (!flag_bits && wire->width != 1 && widthparam.empty()) {
					log("Don't map multi-bit port %s.%s: Missing option -widthparam or -bits.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name));
					continue;
				}

				log("Mapping port %s.%s using %s.\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire->name), celltype.c_str());

				if (flag_bits)
				{
					for (int i = 0; i < wire->width; i++)
					{
						if (skip_bit_indices.count(i))
							continue;

						SigBit wire_bit(wire, i);

						RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(celltype));
						cell->setPort(RTLIL::escape_id(portname_int), wire_bit);

						if (!portname_pad.empty())
							rewrite_bits[wire][i] = make_pair(cell, RTLIL::escape_id(portname_pad));
						if (!widthparam.empty())
							cell->parameters[RTLIL::escape_id(widthparam)] = RTLIL::Const(1);
						if (!nameparam.empty())
							cell->parameters[RTLIL::escape_id(nameparam)] = RTLIL::Const(stringf("%s[%d]", RTLIL::id2cstr(wire->name), i));
						cell->attributes[ID::keep] = RTLIL::Const(1);
					}
				}
				else
				{
					RTLIL::Cell *cell = module->addCell(NEW_ID, RTLIL::escape_id(celltype));
					cell->setPort(RTLIL::escape_id(portname_int), RTLIL::SigSpec(wire));

					if (!portname_pad.empty()) {
						RTLIL::Wire *new_wire = NULL;
						new_wire = module->addWire(NEW_ID, wire);
						module->swap_names(new_wire, wire);
						wire->attributes.clear();
						cell->setPort(RTLIL::escape_id(portname_pad), RTLIL::SigSpec(new_wire));
					}
					if (!widthparam.empty())
						cell->parameters[RTLIL::escape_id(widthparam)] = RTLIL::Const(wire->width);
					if (!nameparam.empty())
						cell->parameters[RTLIL::escape_id(nameparam)] = RTLIL::Const(RTLIL::id2cstr(wire->name));
					cell->attributes[ID::keep] = RTLIL::Const(1);
				}

				if (!rewrite_bits.count(wire)) {
					wire->port_id = 0;
					wire->port_input = false;
					wire->port_output = false;
				}
			}

			for (auto &it : rewrite_bits) {
				RTLIL::Wire *wire = it.first;
				RTLIL::Wire *new_wire = module->addWire(NEW_ID, wire);
				module->swap_names(new_wire, wire);
				wire->attributes.clear();
				for (int i = 0; i < wire->width; i++)
				{
					SigBit wire_bit(wire, i);
					if (!it.second.count(i)) {
						if (wire->port_output)
							module->connect(SigSpec(new_wire, i), SigSpec(wire, i));
						else
							module->connect(SigSpec(wire, i), SigSpec(new_wire, i));
					} else {
						auto &new_conn = it.second.at(i);
						new_conn.first->setPort(new_conn.second, RTLIL::SigSpec(new_wire, i));
					}
				}

				if (wire->port_output) {
					auto jt = new_wire->attributes.find(ID(init));
					// For output ports, move \init attributes from old wire to new wire
					if (jt != new_wire->attributes.end()) {
						wire->attributes[ID(init)] = std::move(jt->second);
						new_wire->attributes.erase(jt);
					}
				}

				wire->port_id = 0;
				wire->port_input = false;
				wire->port_output = false;
			}

			module->fixup_ports();
		}
	}
} IopadmapPass;

PRIVATE_NAMESPACE_END
