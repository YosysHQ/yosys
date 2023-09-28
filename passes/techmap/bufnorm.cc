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
		log("has exactly one driving cell port, and aliasing wires are buffered using\n");
		log("buffer cells, than can be chained in a canonical order.\n");
		log("\n");
		log("Running 'bufnorm' on the whole design enters 'buffered-normalized mode'.\n");
		log("The commands 'bufnorm -conn' exits 'buffered-normalized mode' again.\n");
		log("\n");
		log("    -bits\n");
		log("        Create single-bit $_BUF_ cells instead of multi-bit $pos cells.\n");
		log("\n");
		log("    -chain\n");
		log("        Chain all alias wires. By default only wires with the 'keep'\n");
		log("        attribute on them are chained.\n");
		log("\n");
		log("    -chain-outputs\n");
		log("        Chain ouput ports. (Uneffected by -flat.)\n");
		log("\n");
		log("    -flat\n");
		log("        Do not chain any wires, not even the ones marked with 'keep'.\n");
		log("\n");
		log("    -nosticky\n");
		log("        Disable 'sticky' behavior of output ports already driving whole\n");
		log("        wires, and always enforce canonical sort order instead.\n");
		log("\n");
		log("    -alphasort\n");
		log("        Strictly use alphanumeric sort for chain-order. (Default is\n");
		log("        to chain 'keep' wires first, then ports in declaration order,\n");
		log("        and then the other wires in alphanumeric sort order.)\n");
		log("\n");
		log("    -conn\n");
		log("        Remove buffers and exit 'buffered-normalized mode'.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing BUFNORM pass (convert to buffer-normalized form).\n");

		bool connections_mode = false, bits_mode = false;
		bool chain_mode = false, flat_mode = false, nosticky_mode = false;
		bool chain_outputs_mode = false, alphasort_mode = false;
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
			if (arg == "-chain") {
				chain_mode = true;
				continue;
			}
			if (arg == "-chain-outputs") {
				chain_outputs_mode = true;
				continue;
			}
			if (arg == "-flat") {
				flat_mode = true;
				continue;
			}
			if (arg == "-nosticky") {
				nosticky_mode = true;
				continue;
			}
			if (arg == "-alphasort") {
				alphasort_mode = true;
				continue;
			}
			//if (arg == "-buf" && argidx+3 < args.size()) {
			//	buf_celltype = RTLIL::escape_id(args[++argidx]);
			//	buf_inport = RTLIL::escape_id(args[++argidx]);
			//	buf_outport = RTLIL::escape_id(args[++argidx]);
			//	continue;
			//}
			break;
		}
		extra_args(args, argidx, design);

		if (chain_mode && flat_mode)
			log_cmd_error("Options -chain and -flat are exclusive.\n");

		if (buf_celltype == IdString())
			buf_celltype = bits_mode ? ID($_BUF_) : ID($pos);

		for (auto module : design->selected_modules())
		{
			log("Buffer-normalizing module %s.\n", log_id(module));

			SigMap sigmap(module);
			module->new_connections({});

			{
				vector<Cell*> old_buffers;
				for (auto cell : module->cells())
				{
					if (cell->type != buf_celltype)
						continue;

					SigSpec insig = sigmap(cell->getPort(buf_inport));
					SigSpec outsig = sigmap(cell->getPort(buf_outport));
					for (int i = 0; i < GetSize(insig) && i < GetSize(outsig); i++)
						sigmap.add(insig[i], outsig[i]);
					old_buffers.push_back(cell);
				}
				for (auto cell : old_buffers)
					module->remove(cell);
			}

			dict<SigBit, pool<Wire*>> bit2wires;
			dict<SigSpec, pool<Wire*>> whole_wires;
			dict<SigBit, SigBit> mapped_bits;
			pool<Wire*> unmapped_wires;

			for (auto wire : module->wires())
			{
				SigSpec keysig = sigmap(wire);
				whole_wires[keysig].insert(wire);

				for (auto keybit : sigmap(wire))
					bit2wires[keybit].insert(wire);

				if (wire->port_input) {
					log("  primary input: %s\n", log_id(wire));
					for (auto bit : SigSpec(wire))
						mapped_bits[sigmap(bit)] = bit;
				} else {
					unmapped_wires.insert(wire);
				}
			}

			struct {
				bool alphasort_mode;
				bool operator()(Wire *a, Wire *b) const
				{
					if (!alphasort_mode)
					{
						// Wires with keep attribute first
						bool keep_a = a->get_bool_attribute(ID::keep);
						bool keep_b = a->get_bool_attribute(ID::keep);
						if (keep_a != keep_b) return keep_a;

						// Ports before non-ports
						if ((a->port_id != 0) != (b->port_id != 0))
							return a->port_id != 0;

						// Ports in declaration order
						if (a->port_id != b->port_id)
							return a->port_id < b->port_id;
					}

					// Nets with public names first
					if (a->name.isPublic() != b->name.isPublic())
						return a->name.isPublic();

					// Otherwise just sort by name alphanumerically
					return a->name.str() < b->name.str();
				}
			} compareWires;
			compareWires.alphasort_mode = alphasort_mode;

			for (auto cell : module->cells())
			{
				for (auto &conn : cell->connections())
				{
					if (!cell->output(conn.first))
						continue;

					Wire *w = nullptr;

					if (!nosticky_mode && conn.second.is_wire())
						w = conn.second.as_wire();

					if (w == nullptr)
					{
						SigSpec keysig = sigmap(conn.second);
						auto it = whole_wires.find(keysig);
						if (it != whole_wires.end()) {
							it->second.sort(compareWires);
							w = *(it->second.begin());
						} else {
							w = module->addWire(NEW_ID, GetSize(conn.second));
							for (int i = 0; i < GetSize(w); i++)
								sigmap.add(SigBit(w, i), keysig[i]);
						}
					}

					if (w->name.isPublic())
						log("  directly driven by cell %s port %s: %s\n",
								log_id(cell), log_id(conn.first), log_id(w));

					for (auto bit : SigSpec(w))
						mapped_bits[sigmap(bit)] = bit;
					unmapped_wires.erase(w);

					cell->setPort(conn.first, w);
				}
			}

			pool<Cell*> added_buffers;

			unmapped_wires.sort(compareWires);
			for (auto wire : unmapped_wires)
			{
				bool chain_this_wire = chain_mode;
				if (!flat_mode && wire->get_bool_attribute(ID::keep))
					chain_this_wire = true;
				if (chain_outputs_mode && wire->port_output)
					chain_this_wire = true;

				SigSpec keysig = sigmap(wire), insig = wire, outsig = wire;
				for (int i = 0; i < GetSize(insig); i++)
					insig[i] = mapped_bits.at(keysig[i], State::Sx);
				if (chain_this_wire) {
					for (int i = 0; i < GetSize(outsig); i++)
						mapped_bits[keysig[i]] = outsig[i];
				}

				log("  %s %s for %s -> %s\n",
						chain_this_wire ? "chaining" : "adding",
						connections_mode ? "connection" : "buffer",
						log_signal(insig), log_signal(outsig));

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
							added_buffers.insert(c);
						}
					} else {
						Cell *c = module->addCell(NEW_ID, buf_celltype);
						c->setPort(buf_inport, insig);
						c->setPort(buf_outport, outsig);
						c->fixup_parameters();
						added_buffers.insert(c);
					}
				}
			}

			for (auto cell : module->cells())
			{
				if (added_buffers.count(cell))
					continue;

				for (auto &conn : cell->connections())
				{
					if (cell->output(conn.first))
						continue;

					SigSpec newsig = conn.second;
					for (auto &bit : newsig)
						bit = mapped_bits[sigmap(bit)];

					if (conn.second != newsig) {
						log("  fixing input signal on cell %s port %s: %s\n",
								log_id(cell), log_id(conn.first), log_signal(newsig));
						cell->setPort(conn.first, newsig);
					}
				}
			}
		}
	}
} BufnormPass;

PRIVATE_NAMESPACE_END
