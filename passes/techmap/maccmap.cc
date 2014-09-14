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
#include "kernel/macc.h"

extern void maccmap(RTLIL::Module *module, RTLIL::Cell *cell, bool unmap = false);

struct MaccmapWorker
{
	std::vector<std::set<RTLIL::SigBit>> bits;
	RTLIL::Module *module;
	int width;

	MaccmapWorker(RTLIL::Module *module, int width) : module(module), width(width)
	{
		bits.resize(width);
	}

	void add(RTLIL::SigBit bit, int position)
	{
		if (position >= width || bit == RTLIL::S0)
			return;

		if (bits.at(position).count(bit)) {
			bits.at(position).erase(bit);
			add(bit, position+1);
		} else {
			bits.at(position).insert(bit);
		}
	}

	void add(RTLIL::SigSpec a, bool is_signed, bool do_subtract)
	{
		a.extend(width, is_signed);

		if (do_subtract) {
			a = module->Not(NEW_ID, a);
			add(RTLIL::S1, 0);
		}

		for (int i = 0; i < width; i++)
			add(a[i], i);
	}

	void add(RTLIL::SigSpec a, RTLIL::SigSpec b, bool is_signed, bool do_subtract)
	{
		if (SIZE(a) < SIZE(b))
			std::swap(a, b);

		a.extend(width, is_signed);

		if (SIZE(b) > width)
			b.extend(width, is_signed);

		for (int i = 0; i < SIZE(b); i++)
			if (is_signed && i+1 == SIZE(b))
			{
				a = {module->Not(NEW_ID, a.extract(i, width-i)), RTLIL::SigSpec(0, i)};
				add(module->And(NEW_ID, a, RTLIL::SigSpec(b[i], width)), false, do_subtract);
				add({b[i], RTLIL::SigSpec(0, i)}, false, do_subtract);
			}
			else
			{
				add(module->And(NEW_ID, a, RTLIL::SigSpec(b[i], width)), false, do_subtract);
				a = {a.extract(0, width-1), RTLIL::S0};
			}
	}

	void fulladd(RTLIL::SigSpec &in1, RTLIL::SigSpec &in2, RTLIL::SigSpec &in3, RTLIL::SigSpec &out1, RTLIL::SigSpec &out2)
	{
		int start_index = 0, stop_index = SIZE(in1);

		while (start_index < stop_index && in1[start_index] == RTLIL::S0 && in2[start_index] == RTLIL::S0 && in3[start_index] == RTLIL::S0)
			start_index++;

		while (start_index < stop_index && in1[stop_index-1] == RTLIL::S0 && in2[stop_index-1] == RTLIL::S0 && in3[stop_index-1] == RTLIL::S0)
			stop_index--;

		if (start_index == stop_index)
		{
			out1 = RTLIL::SigSpec(0, SIZE(in1));
			out2 = RTLIL::SigSpec(0, SIZE(in1));
		}
		else
		{
			RTLIL::SigSpec out_zeros_lsb(0, start_index), out_zeros_msb(0, SIZE(in1)-stop_index);

			in1 = in1.extract(start_index, stop_index-start_index);
			in2 = in2.extract(start_index, stop_index-start_index);
			in3 = in3.extract(start_index, stop_index-start_index);

			int width = SIZE(in1);
			RTLIL::Wire *w1 = module->addWire(NEW_ID, width);
			RTLIL::Wire *w2 = module->addWire(NEW_ID, width);

			RTLIL::Cell *cell = module->addCell(NEW_ID, "$fa");
			cell->setParam("\\WIDTH", width);
			cell->setPort("\\A", in1);
			cell->setPort("\\B", in2);
			cell->setPort("\\C", in3);
			cell->setPort("\\Y", w1);
			cell->setPort("\\X", w2);

			out1 = {out_zeros_msb, w1, out_zeros_lsb};
			out2 = {out_zeros_msb, w2, out_zeros_lsb};
		}
	}

	int tree_bit_slots(int n)
	{
	#if 0
		int retval = 0;
		while (n > 2) {
			retval += n / 3;
			n = 2*(n / 3) + (n % 3);
		}
		return retval;
	#else
		return std::max(n - 2, 0);
	#endif
	}

	RTLIL::SigSpec synth()
	{
		std::vector<RTLIL::SigSpec> summands;
		std::vector<RTLIL::SigBit> tree_sum_bits;
		int unique_tree_bits = 0;

		while (1)
		{
			RTLIL::SigSpec summand(0, width);
			bool got_data_bits = false;

			for (int i = 0; i < width; i++)
				if (!bits.at(i).empty()) {
					auto it = bits.at(i).begin();
					summand[i] = *it;
					bits.at(i).erase(it);
					got_data_bits = true;
				}

			if (!got_data_bits)
				break;

			summands.push_back(summand);
			int free_bit_slots = tree_bit_slots(SIZE(summands)) - SIZE(tree_sum_bits);

			for (int i = 0; i < width && (1 << i) <= free_bit_slots; i++)
				while (!bits.at(i).empty() && (1 << i) <= free_bit_slots) {
					auto it = bits.at(i).begin();
					RTLIL::SigBit bit = *it;
					bits.at(i).erase(it);
					for (int k = 0; k < (1 << i); k++, free_bit_slots--)
						tree_sum_bits.push_back(bit);
					unique_tree_bits++;
				}
		}

		if (!tree_sum_bits.empty())
			log("  packed %d (%d) bits into adder tree\n", SIZE(tree_sum_bits), unique_tree_bits);

		if (SIZE(summands) == 0)
			return RTLIL::SigSpec(0, width);

		if (SIZE(summands) == 1)
			return summands.front();

		while (SIZE(summands) > 2)
		{
			std::vector<RTLIL::SigSpec> new_summands;
			for (int i = 0; i < SIZE(summands); i += 3)
				if (i+2 < SIZE(summands)) {
					RTLIL::SigSpec in1 = summands[i];
					RTLIL::SigSpec in2 = summands[i+1];
					RTLIL::SigSpec in3 = summands[i+2];
					RTLIL::SigSpec out1, out2;
					fulladd(in1, in2, in3, out1, out2);
					RTLIL::SigBit extra_bit = RTLIL::S0;
					if (!tree_sum_bits.empty()) {
						extra_bit = tree_sum_bits.back();
						tree_sum_bits.pop_back();
					}
					new_summands.push_back(out1);
					new_summands.push_back({out2.extract(0, width-1), extra_bit});
				} else {
					new_summands.push_back(summands[i]);
					i -= 2;
				}
			summands.swap(new_summands);
		}

		log_assert(tree_sum_bits.empty());

		RTLIL::Cell *c = module->addCell(NEW_ID, "$alu");
		c->setPort("\\A", summands.front());
		c->setPort("\\B", summands.back());
		c->setPort("\\CI", RTLIL::S0);
		c->setPort("\\BI", RTLIL::S0);
		c->setPort("\\Y", module->addWire(NEW_ID, width));
		c->setPort("\\X", module->addWire(NEW_ID, width));
		c->setPort("\\CO", module->addWire(NEW_ID, width));
		c->fixup_parameters();

		return c->getPort("\\Y");
	}
};

void maccmap(RTLIL::Module *module, RTLIL::Cell *cell, bool unmap)
{
	int width = SIZE(cell->getPort("\\Y"));

	Macc macc;
	macc.from_cell(cell);

	RTLIL::SigSpec all_input_bits;
	all_input_bits.append(cell->getPort("\\A"));
	all_input_bits.append(cell->getPort("\\B"));

	if (all_input_bits.to_sigbit_set().count(RTLIL::Sx)) {
		module->connect(cell->getPort("\\Y"), RTLIL::SigSpec(RTLIL::Sx, width));
		return;
	}

	for (auto &port : macc.ports)
		if (SIZE(port.in_b) == 0)
			log("  %s %s (%d bits, %s)\n", port.do_subtract ? "sub" : "add", log_signal(port.in_a),
					SIZE(port.in_a), port.is_signed ? "signed" : "unsigned");
		else
			log("  %s %s * %s (%dx%d bits, %s)\n", port.do_subtract ? "sub" : "add", log_signal(port.in_a), log_signal(port.in_b),
					SIZE(port.in_a), SIZE(port.in_b), port.is_signed ? "signed" : "unsigned");

	if (SIZE(macc.bit_ports) != 0)
		log("  add bits %s (%d bits)\n", log_signal(macc.bit_ports), SIZE(macc.bit_ports));

	if (unmap)
	{
		typedef std::pair<RTLIL::SigSpec, bool> summand_t;
		std::vector<summand_t> summands;

		for (auto &port : macc.ports) {
			summand_t this_summand;
			if (SIZE(port.in_b)) {
				this_summand.first = module->addWire(NEW_ID, width);
				module->addMul(NEW_ID, port.in_a, port.in_b, this_summand.first, port.is_signed);
			} else if (SIZE(port.in_a) != width) {
				this_summand.first = module->addWire(NEW_ID, width);
				module->addPos(NEW_ID, port.in_a, this_summand.first, port.is_signed);
			} else {
				this_summand.first = port.in_a;
			}
			this_summand.second = port.do_subtract;
			summands.push_back(this_summand);
		}

		for (auto &bit : macc.bit_ports)
			summands.push_back(summand_t(bit, false));

		if (SIZE(summands) == 0)
			summands.push_back(summand_t(RTLIL::SigSpec(0, width), false));

		while (SIZE(summands) > 1)
		{
			std::vector<summand_t> new_summands;
			for (int i = 0; i < SIZE(summands); i += 2) {
				if (i+1 < SIZE(summands)) {
					summand_t this_summand;
					this_summand.first = module->addWire(NEW_ID, width);
					this_summand.second = summands[i].second && summands[i+1].second;
					if (summands[i].second == summands[i+1].second)
						module->addAdd(NEW_ID, summands[i].first, summands[i+1].first, this_summand.first);
					else if (summands[i].second)
						module->addSub(NEW_ID, summands[i+1].first, summands[i].first, this_summand.first);
					else if (summands[i+1].second)
						module->addSub(NEW_ID, summands[i].first, summands[i+1].first, this_summand.first);
					else
						log_abort();
					new_summands.push_back(this_summand);
				} else
					new_summands.push_back(summands[i]);
			}
			summands.swap(new_summands);
		}

		if (summands.front().second)
			module->addNeg(NEW_ID, summands.front().first, cell->getPort("\\Y"));
		else
			module->connect(cell->getPort("\\Y"), summands.front().first);
	}
	else
	{
		MaccmapWorker worker(module, width);

		for (auto &port : macc.ports)
			if (SIZE(port.in_b) == 0)
				worker.add(port.in_a, port.is_signed, port.do_subtract);
			else
				worker.add(port.in_a, port.in_b, port.is_signed, port.do_subtract);

		for (auto &bit : macc.bit_ports)
			worker.add(bit, 0);

		module->connect(cell->getPort("\\Y"), worker.synth());
	}
}

struct MaccmapPass : public Pass {
	MaccmapPass() : Pass("maccmap", "mapping macc cells") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    maccmap [-unmap] [selection]\n");
		log("\n");
		log("This pass maps $macc cells to yosys gate primitives. When the -unmap option is\n");
		log("used then the $macc cell is mapped to $and, $sub, etc. cells instead.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool unmap_mode = false;

		log_header("Executing MACCMAP pass (map $macc cells).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			if (args[argidx] == "-unmap") {
				unmap_mode = true;
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules())
		for (auto cell : mod->selected_cells())
			if (cell->type == "$macc") {
				log("Mapping %s.%s (%s).\n", log_id(mod), log_id(cell), log_id(cell->type));
				maccmap(mod, cell, unmap_mode);
				mod->remove(cell);
			}
	}
} MaccmapPass;
 
