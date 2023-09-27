/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

struct BufnormPass : public Pass {
	BufnormPass() : Pass("bufnorm", "convert design into buffered-normalized form") { }
	void help() override
	{
		log("\n");
		log("    bufnorm [options] [selection]\n");
		log("\n");
		log("Insert buffer cells into the design as needed, to make sure that each wire\n");
		log("has exactly one driving cell port, and aliasing wires are buffered using a\n");
		log("chain of buffers in canonical order.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BUFNORM pass (convert to buffer-normalized form).\n");

		bool connections_mode = false, bits_mode = false;
		IdString buf_celltype, buf_inport = ID::A, buf_outport = ID::Y;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			std::string arg = args[argidx];
			if (arg == "-conn") {
				connections_mode = true;
				continue;
			}
			if (arg == "-bits") {
				bits_mode = true;
				continue;
			}
			if (arg == "-buf" && argidx+3 < args.size()) {
				buf_celltype = RTLIL::escape_id(args[++argidx]);
				buf_inport = RTLIL::escape_id(args[++argidx]);
				buf_outport = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (buf_celltype == IdString())
			buf_celltype = bits_mode ? ID($_BUF_) : ID($pos);

		for (auto module : design->selected_modules())
		{
			SigMap sigmap(module);
			module->new_connections({});

			{
				vector<Cell*> old_buffers;
				for (auto cell : module->cells())
				{
					if (cell->type == buf_celltype)
					{
						SigSpec insig = sigmap(cell->getPort(buf_inport));
						SigSpec outsig = sigmap(cell->getPort(buf_outport));
						for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
							sigmap.add(insig[i], outsig[i]);
						old_buffers.push_back(cell);
					}
					else
					{
						for (auto &conn : cell->connections())
						{
							if (!cell->output(conn.first) || conn.second.is_wire())
								continue;
							SigSpec insig = module->addWire(NEW_ID, GetSize(conn.second));
							SigSpec outsig = sigmap(conn.second);
							for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
								sigmap.add(insig[i], outsig[i]);
							cell->setPort(conn.first, insig);
						}
					}
				}
				for (auto cell : old_buffers)
					module->remove(cell);
			}

			dict<SigBit, pool<Wire*>> bit2wires;
			dict<SigBit, SigBit> mapped_bits;
			pool<Wire*> unmapped_wires;

			for (auto wire : module->wires())
			{
				for (auto key : sigmap(wire))
					bit2wires[key].insert(wire);

				if (wire->port_input) {
					for (auto bit : SigSpec(wire))
						mapped_bits[sigmap(bit)] = bit;
				} else {
					unmapped_wires.insert(wire);
				}
			}

			for (auto cell : module->cells())
			{
				for (auto &conn : cell->connections())
				{
					if (!cell->output(conn.first))
						continue;

					for (auto bit : conn.second)
						mapped_bits[sigmap(bit)] = bit;
					unmapped_wires.erase(conn.second.as_wire());
				}
			}

			struct {
				bool operator()(Wire *a, Wire *b) const {
					if (a->port_id != b->port_id)
						return a->port_id < b->port_id;
					return a->name.str() < b->name.str();
				}
			} compareWires;

			unmapped_wires.sort(compareWires);

			for (auto wire : unmapped_wires)
			{
				SigSpec keysig = sigmap(wire), insig = wire, outsig = wire;
				for (int i = 0; i < GetSize(insig); i++)
					insig[i] = mapped_bits.at(keysig[i], State::Sx);
				for (int i = 0; i < GetSize(outsig); i++)
					mapped_bits[keysig[i]] = outsig[i];

				if (connections_mode) {
					if (bits_mode) {
						for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
							module->connect(outsig[i], insig[i]);
					} else {
						module->connect(outsig, insig);
					}
				} else {
					if (bits_mode) {
						for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++) {
							Cell *c = module->addCell(NEW_ID, buf_celltype);
							c->setPort(buf_inport, insig[i]);
							c->setPort(buf_outport, outsig[i]);
							c->fixup_parameters();
						}
					} else {
						Cell *c = module->addCell(NEW_ID, buf_celltype);
						c->setPort(buf_inport, insig);
						c->setPort(buf_outport, outsig);
						c->fixup_parameters();
					}
				}
			}
		}
	}
} BufnormPass;

PRIVATE_NAMESPACE_END
