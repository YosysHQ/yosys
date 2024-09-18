/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C)  Martin Povišer <povik@cutebit.org>
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

uint32_t read_be32(std::istream &f) {
	return ((uint32_t) f.get() << 24) |
		((uint32_t) f.get() << 16) | 
		((uint32_t) f.get() << 8) | (uint32_t) f.get();
}

IdString read_idstring(std::istream &f)
{
	std::string str;
	std::getline(f, str, '\0');
	if (!f.good())
		log_error("failed to read string\n");
	return RTLIL::escape_id(str);
}

struct Xaiger2Frontend : public Frontend {
	Xaiger2Frontend() : Frontend("xaiger2", "read XAIGER file (new)") {}

	void read_sc_mapping(std::istream *&f, std::string filename, std::vector<std::string> args, Design *design)
	{
		IdString module_name;
		std::string map_filename;

		size_t argidx;
		for (argidx = 2; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-module_name" && argidx + 1 < args.size()) {
				module_name = RTLIL::escape_id(args[++argidx]);
				continue;
			}
			if (arg == "-map2" && argidx + 1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx, true);

		if (map_filename.empty())
			log_error("A '-map2' argument required\n");
		if (module_name.empty())
			log_error("A '-module_name' argument required\n");

		Module *module = design->module(module_name);
		if (!module)
			log_error("Module '%s' not found\n", log_id(module_name));

		std::ifstream map_file;
		map_file.open(map_filename);
		if (!map_file)
			log_error("Failed to open map file '%s'\n", map_filename.c_str());

		unsigned int M, I, L, O, A;
		std::string header;
		if (!(*f >> header >> M >> I >> L >> O >> A) || header != "aig")
			log_error("Bad header\n");
		std::string line;
		std::getline(*f, line);
		log_debug("M=%u I=%u L=%u O=%u A=%u\n", M, I, L, O, A);

		if (L != 0)
			log_error("Latches unsupported\n");
		if (I + L + A != M)
			log_error("Inconsistent header\n");

		std::vector<int> outputs;
		for (int i = 0; i < O; i++) {
			int po;
			*f >> po;
			log_assert(f->get() == '\n');
			outputs.push_back(po);
		}

		std::vector<SigBit> bits(2 + 2*M, RTLIL::Sm);
		bits[0] = RTLIL::S0;
		bits[1] = RTLIL::S1;

		std::string type;
		while (map_file >> type) {
			if (type == "pi") {
				int pi_idx;
				int woffset;
				std::string name;
				if (!(map_file >> pi_idx >> woffset >> name))
					log_error("Bad map file (1)\n");
				int lit = (2 * pi_idx) + 2;
				if (lit < 0 || lit >= bits.size())
					log_error("Bad map file (2)\n");
				Wire *w = module->wire(name);
				if (!w || woffset < 0 || woffset >= w->width)
					log_error("Map file references non-existent signal bit %s[%d]\n",
							  name.c_str(), woffset);
				bits[lit] = SigBit(w, woffset);
			} else {
				std::string scratch;
				std::getline(map_file, scratch);
			}
		}

		for (int i = 0; i < A; i++) {
			while (f->get() & 0x80 && !f->eof());
			while (f->get() & 0x80 && !f->eof());
		}

		if (f->get() != 'c')
			log_error("Missing 'c' ahead of extensions\n");
		if (f->peek() == '\n')
			f->get();

		bool read_mapping = false;
		uint32_t no_cells, no_instances;
		for (int c = f->get(); c != EOF; c = f->get()) {
			if (c == 'M') {
				uint32_t len = read_be32(*f);
				read_mapping = true;

				no_cells = read_be32(*f);
				no_instances = read_be32(*f);

				log_debug("M: len=%u no_cells=%u no_instances=%u\n", len, no_cells, no_instances);

				struct MappingCell {
					RTLIL::IdString type;
					RTLIL::IdString out;
					std::vector<RTLIL::IdString> ins;
				};
				std::vector<MappingCell> cells;
				cells.resize(no_cells);

				for (unsigned i = 0; i < no_cells; ++i) {
					auto &cell = cells[i];
					cell.type = read_idstring(*f);
					cell.out = read_idstring(*f);
					uint32_t nins = read_be32(*f);
					for (uint32_t j = 0; j < nins; j++)
						cell.ins.push_back(read_idstring(*f));
					log_debug("M: Cell %s (out %s, ins", log_id(cell.type), log_id(cell.out));
					for (auto in : cell.ins)
						log_debug(" %s", log_id(in));
					log_debug(")\n");
				}

				for (unsigned i = 0; i < no_instances; ++i) {
					uint32_t cell_id = read_be32(*f);
					uint32_t out_lit = read_be32(*f);

					log_assert(out_lit < bits.size());
					log_assert(bits[out_lit] == RTLIL::Sm);
					log_assert(cell_id < cells.size());
					auto &cell = cells[cell_id];
					Cell *instance = module->addCell(NEW_ID, cell.type);
					auto out_w = module->addWire(NEW_ID);
					instance->setPort(cell.out, out_w);
					bits[out_lit] = out_w;
					for (auto in : cell.ins) {
						uint32_t in_lit = read_be32(*f);
						log_assert(out_lit < bits.size());
						log_assert(bits[in_lit] != RTLIL::Sm);
						instance->setPort(in, bits[in_lit]);
					}
				}
			} else if (c == '\n') {
				break;
			} else {
				uint32_t len = read_be32(*f);
				f->ignore(len);
				log_debug("section '%c' (%d): ignoring %d bytes\n", c, c, len);
			}
		}

		if (!read_mapping)
			log_error("Missing mapping (no 'M' section)\n");

		while (true) {
			std::string scratch;
			std::getline(*f, scratch);
			if (f->eof())
				break;
			log_assert(!f->fail());
			log("input file: %s\n", scratch.c_str());
		}

		log("Read %d instances with cell library of size %d.\n",
			no_instances, no_cells);

		// TODO
		map_file.close();
		map_file.open(map_filename);
		while (map_file >> type) {
			if (type == "po") {
				int po_idx;
				int woffset;
				std::string name;
				if (!(map_file >> po_idx >> woffset >> name))
					log_error("Bad map file (3)\n");
				if (po_idx < 0 || po_idx >= outputs.size())
					log_error("Bad map file (4)\n");
				int lit = outputs[po_idx];
				if (lit < 0 || lit >= bits.size())
					log_error("Bad map file (5)\n");
				if (bits[lit] == RTLIL::Sm)
					log_error("Bad map file (6)\n");
				Wire *w = module->wire(name);
				if (!w || woffset < 0 || woffset >= w->width)
					log_error("Map file references non-existent signal bit %s[%d]\n",
							  name.c_str(), woffset);
				module->connect(SigBit(w, woffset), bits[lit]);
			} else if (type == "pseudopo") {
				int po_idx;
				int poffset;
				std::string box_name;
				std::string box_port;
				if (!(map_file >> po_idx >> poffset >> box_name >> box_port))
					log_error("Bad map file (7)\n");
				if (po_idx < 0 || po_idx >= outputs.size())
					log_error("Bad map file (8)\n");
				int lit = outputs[po_idx];
				if (lit < 0 || lit >= bits.size())
					log_error("Bad map file (9)\n");
				if (bits[lit] == RTLIL::Sm)
					log_error("Bad map file (10)\n");
				Cell *cell = module->cell(box_name);
				if (!cell || !cell->hasPort(box_port))
					log_error("Map file references non-existent box port %s/%s\n",
							  box_name.c_str(), box_port.c_str());
				SigSpec &port = cell->connections_[box_port];
				if (poffset < 0 || poffset >= port.size())
					log_error("Map file references non-existent box port bit %s/%s[%d]\n",
							  box_name.c_str(), box_port.c_str(), poffset);
				port[poffset] = bits[lit];
			} else {
				std::string scratch;
				std::getline(map_file, scratch);
			}
		}
	}

	void execute(std::istream *&f, std::string filename, std::vector<std::string> args, Design *design) override
	{
		log_header(design, "Executing XAIGER2 frontend.\n");

		if (args.size() > 1 && args[1] == "-sc_mapping") {
			read_sc_mapping(f, filename, args, design);
			return;
		}

		log_cmd_error("Mode '-sc_mapping' must be selected\n");
	}
} Xaiger2Frontend;

PRIVATE_NAMESPACE_END
