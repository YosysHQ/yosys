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

struct SplitcellsWorker
{
	Module *module;
	SigMap sigmap;
	dict<SigBit, tuple<IdString,IdString,int>> bit_drivers_db;
	dict<SigBit, pool<tuple<IdString,IdString,int>>> bit_users_db;

	SplitcellsWorker(Module *module) : module(module), sigmap(module)
	{
		for (auto cell : module->cells()) {
			for (auto conn : cell->connections()) {
				if (!cell->output(conn.first)) continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit(sigmap(conn.second[i]));
					bit_drivers_db[bit] = tuple<IdString,IdString,int>(cell->name, conn.first, i);
				}
			}
		}

		for (auto cell : module->cells()) {
			for (auto conn : cell->connections()) {
				if (!cell->input(conn.first)) continue;
				for (int i = 0; i < GetSize(conn.second); i++) {
					SigBit bit(sigmap(conn.second[i]));
					if (!bit_drivers_db.count(bit)) continue;
					bit_users_db[bit].insert(tuple<IdString,IdString,int>(cell->name,
							conn.first, i-std::get<2>(bit_drivers_db[bit])));
				}
			}
		}

		for (auto wire : module->wires()) {
			if (!wire->name.isPublic()) continue;
			SigSpec sig(sigmap(wire));
			for (int i = 0; i < GetSize(sig); i++) {
				SigBit bit(sig[i]);
				if (!bit_drivers_db.count(bit)) continue;
				bit_users_db[bit].insert(tuple<IdString,IdString,int>(wire->name,
						IdString(), i-std::get<2>(bit_drivers_db[bit])));
			}
		}
	}

	int split(Cell *cell, const std::string &format)
	{
		if (cell->type.in("$and", "$mux", "$not", "$or", "$pmux", "$xnor", "$xor"))
		{
			SigSpec outsig = sigmap(cell->getPort(ID::Y));
			if (GetSize(outsig) <= 1) return 0;

			std::vector<int> slices;
			slices.push_back(0);

			int width = GetSize(outsig);
			width = std::min(width, GetSize(cell->getPort(ID::A)));
			if (cell->hasPort(ID::B))
				width = std::min(width, GetSize(cell->getPort(ID::B)));

			for (int i = 1; i < width; i++) {
				auto &last_users = bit_users_db[outsig[slices.back()]];
				auto &this_users = bit_users_db[outsig[i]];
				if (last_users != this_users) slices.push_back(i);
			}
			if (GetSize(slices) <= 1) return 0;
			slices.push_back(GetSize(outsig));

			log("Splitting %s cell %s/%s into %d slices:\n", log_id(cell->type), log_id(module), log_id(cell), GetSize(slices)-1);
			for (int i = 1; i < GetSize(slices); i++)
			{
				int slice_msb = slices[i]-1;
				int slice_lsb = slices[i-1];

				IdString slice_name = module->uniquify(cell->name.str() + (slice_msb == slice_lsb ?
						stringf("%c%d%c", format[0], slice_lsb, format[1]) :
						stringf("%c%d%c%d%c", format[0], slice_msb, format[2], slice_lsb, format[1])));

				Cell *slice = module->addCell(slice_name, cell);

				auto slice_signal = [&](SigSpec old_sig) -> SigSpec {
					SigSpec new_sig;
					for (int i = 0; i < GetSize(old_sig); i += GetSize(outsig)) {
						int offset = i+slice_lsb;
						int length = std::min(GetSize(old_sig)-offset, slice_msb-slice_lsb+1);
						new_sig.append(old_sig.extract(offset, length));
					}
					return new_sig;
				};

				slice->setPort(ID::A, slice_signal(slice->getPort(ID::A)));
				if (slice->hasParam(ID::A_WIDTH))
					slice->setParam(ID::A_WIDTH, GetSize(slice->getPort(ID::A)));

				if (slice->hasPort(ID::B)) {
					slice->setPort(ID::B, slice_signal(slice->getPort(ID::B)));
					if (slice->hasParam(ID::B_WIDTH))
						slice->setParam(ID::B_WIDTH, GetSize(slice->getPort(ID::B)));
				}

				slice->setPort(ID::Y, slice_signal(slice->getPort(ID::Y)));
				if (slice->hasParam(ID::Y_WIDTH))
					slice->setParam(ID::Y_WIDTH, GetSize(slice->getPort(ID::Y)));
				if (slice->hasParam(ID::WIDTH))
					slice->setParam(ID::WIDTH, GetSize(slice->getPort(ID::Y)));

				log("  slice %d: %s => %s\n", i, log_id(slice_name), log_signal(slice->getPort(ID::Y)));
			}

			module->remove(cell);
			return GetSize(slices)-1;
		}

		if (cell->type.in("$ff", "$dff", "$dffe", "$dffsr", "$dffsre", "$adff", "$adffe", "$aldffe",
				"$sdff", "$sdffce", "$sdffe", "$dlatch", "$dlatchsr", "$adlatch"))
		{
			auto splitports = {ID::D, ID::Q, ID::AD, ID::SET, ID::CLR};
			auto splitparams = {ID::ARST_VALUE, ID::SRST_VALUE};

			SigSpec outsig = sigmap(cell->getPort(ID::Q));
			if (GetSize(outsig) <= 1) return 0;
			int width = GetSize(outsig);

			std::vector<int> slices;
			slices.push_back(0);

			for (int i = 1; i < width; i++) {
				auto &last_users = bit_users_db[outsig[slices.back()]];
				auto &this_users = bit_users_db[outsig[i]];
				if (last_users != this_users) slices.push_back(i);
			}

			if (GetSize(slices) <= 1) return 0;
			slices.push_back(GetSize(outsig));

			log("Splitting %s cell %s/%s into %d slices:\n", log_id(cell->type), log_id(module), log_id(cell), GetSize(slices)-1);
			for (int i = 1; i < GetSize(slices); i++)
			{
				int slice_msb = slices[i]-1;
				int slice_lsb = slices[i-1];

				IdString slice_name = module->uniquify(cell->name.str() + (slice_msb == slice_lsb ?
						stringf("%c%d%c", format[0], slice_lsb, format[1]) :
						stringf("%c%d%c%d%c", format[0], slice_msb, format[2], slice_lsb, format[1])));

				Cell *slice = module->addCell(slice_name, cell);

				for (IdString portname : splitports) {
					if (slice->hasPort(portname)) {
						SigSpec sig = slice->getPort(portname);
						sig = sig.extract(slice_lsb, slice_msb-slice_lsb+1);
						slice->setPort(portname, sig);
					}
				}

				for (IdString paramname : splitparams) {
					if (slice->hasParam(paramname)) {
						Const val = slice->getParam(paramname);
						val = val.extract(slice_lsb, slice_msb-slice_lsb+1);
						slice->setParam(paramname, val);
					}
				}

				slice->setParam(ID::WIDTH, GetSize(slice->getPort(ID::Q)));

				log("  slice %d: %s => %s\n", i, log_id(slice_name), log_signal(slice->getPort(ID::Q)));
			}

			module->remove(cell);
			return GetSize(slices)-1;
		}

		return 0;
	}
};

struct SplitcellsPass : public Pass {
	SplitcellsPass() : Pass("splitcells", "split up multi-bit cells") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    splitcells [options] [selection]\n");
		log("\n");
		log("This command splits multi-bit cells into smaller chunks, based on usage of the\n");
		log("cell output bits.\n");
		log("\n");
		log("This command operates only in cells such as $or, $and, and $mux, that are easily\n");
		log("cut into bit-slices.\n");
		log("\n");
		log("    -format char1[char2[char3]]\n");
		log("        the first char is inserted between the cell name and the bit index, the\n");
		log("        second char is appended to the cell name. e.g. -format () creates cell\n");
		log("        names like 'mycell(42)'. the 3rd character is the range separation\n");
		log("        character when creating multi-bit cells. the default is '[]:'.\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		std::string format;

		log_header(design, "Executing SPLITCELLS pass (splitting up multi-bit cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-format" && argidx+1 < args.size()) {
				format = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		if (GetSize(format) < 1) format += "[";
		if (GetSize(format) < 2) format += "]";
		if (GetSize(format) < 3) format += ":";

		for (auto module : design->selected_modules())
		{
			int count_split_pre = 0;
			int count_split_post = 0;

			while (1) {
				SplitcellsWorker worker(module);
				bool did_something = false;
				for (auto cell : module->selected_cells()) {
					int n = worker.split(cell, format);
					did_something |= (n != 0);
					count_split_pre += (n != 0);
					count_split_post += n;
				}
				if (!did_something)
					break;
			}

			if (count_split_pre)
				log("Split %d cells in module %s into %d cell slices.\n",
					count_split_pre, log_id(module), count_split_post);
		}
	}
} SplitnetsPass;

PRIVATE_NAMESPACE_END
