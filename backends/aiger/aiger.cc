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

void aiger_encode(std::ostream &f, int x)
{
	log_assert(x >= 0);

	while (x & ~0x7f) {
		f.put((x & 0x7f) | 0x80);
		x = x >> 7;
	}

	f.put(x);
}

struct AigerWriter
{
	Module *module;
	bool zinit_mode;
	SigMap sigmap;

	dict<SigBit, bool> init_map;
	pool<SigBit> input_bits, output_bits;
	dict<SigBit, SigBit> not_map, ff_map;
	dict<SigBit, pair<SigBit, SigBit>> and_map;
	pool<SigBit> initstate_bits;

	vector<pair<int, int>> aig_gates;
	vector<int> aig_latchin, aig_latchinit, aig_outputs;
	int aig_m = 0, aig_i = 0, aig_l = 0, aig_o = 0, aig_a = 0;

	dict<SigBit, int> aig_map;
	dict<SigBit, int> ordered_outputs;
	dict<SigBit, int> ordered_latches;

	dict<SigBit, int> init_inputs;
	int initstate_ff = 0;

	int bit2aig(SigBit bit)
	{
		if (aig_map.count(bit) == 0)
		{
			aig_map[bit] = -1;

			if (initstate_bits.count(bit)) {
				log_assert(initstate_ff > 0);
				aig_map[bit] = initstate_ff;
			} else
			if (not_map.count(bit)) {
				int a = bit2aig(not_map.at(bit)) ^ 1;
				aig_map[bit] = a;
			} else
			if (and_map.count(bit)) {
				auto args = and_map.at(bit);
				int a0 = bit2aig(args.first);
				int a1 = bit2aig(args.second);
				aig_m++, aig_a++;
				aig_map[bit] = 2*aig_m;
				aig_gates.push_back(a0 > a1 ? make_pair(a0, a1) : make_pair(a1, a0));
			}
		}

		log_assert(aig_map.at(bit) >= 0);
		return aig_map.at(bit);
	}

	AigerWriter(Module *module, bool zinit_mode) : module(module), zinit_mode(zinit_mode), sigmap(module)
	{
		for (auto wire : module->wires())
		{
			if (wire->attributes.count("\\init")) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(wire) && i < GetSize(initval); i++)
					init_map[initsig[i]] = initval[i];
			}

			if (wire->port_input)
				for (auto bit : sigmap(wire))
					input_bits.insert(bit);

			if (wire->port_output)
				for (auto bit : sigmap(wire))
					output_bits.insert(bit);
		}

		for (auto cell : module->cells())
		{
			if (cell->type == "$_NOT_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				not_map[Y] = A;
				continue;
			}

			if (cell->type.in("$_FF_", "$_DFF_N_", "$_DFF_P_"))
			{
				SigBit D = sigmap(cell->getPort("\\D").as_bit());
				SigBit Q = sigmap(cell->getPort("\\Q").as_bit());
				ff_map[Q] = D;
				continue;
			}

			if (cell->type == "$_AND_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit B = sigmap(cell->getPort("\\B").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				and_map[Y] = make_pair(A, B);
				continue;
			}

			if (cell->type == "$initstate")
			{
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				initstate_bits.insert(Y);
				continue;
			}

			log_error("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));
		}

		init_map.sort();
		input_bits.sort();
		output_bits.sort();
		not_map.sort();
		ff_map.sort();
		and_map.sort();

		aig_map[State::S0] = 0;
		aig_map[State::S1] = 1;

		for (auto bit : input_bits) {
			aig_m++, aig_i++;
			aig_map[bit] = 2*aig_m;
		}

		if (zinit_mode)
		{
			for (auto it : ff_map) {
				if (init_map.count(it.first))
					continue;
				aig_m++, aig_i++;
				init_inputs[it.first] = 2*aig_m;
			}
		}

		for (auto it : ff_map) {
			aig_m++, aig_l++;
			aig_map[it.first] = 2*aig_m;
			ordered_latches[it.first] = aig_l;
			if (init_map.count(it.first) == 0)
				aig_latchinit.push_back(2);
			else
				aig_latchinit.push_back(init_map.at(it.first) ? 1 : 0);
		}

		if (!initstate_bits.empty() || !init_inputs.empty()) {
			aig_m++, aig_l++;
			initstate_ff = 2*aig_m+1;
			aig_latchinit.push_back(0);
		}

		for (auto it : ff_map)
			aig_latchin.push_back(bit2aig(it.second));

		if (!initstate_bits.empty() || !init_inputs.empty())
			aig_latchin.push_back(1);

		for (auto bit : output_bits) {
			aig_o++;
			ordered_outputs[bit] = aig_o;
			aig_outputs.push_back(bit2aig(bit));
		}
	}

	void write_aiger(std::ostream &f, bool ascii_mode, bool miter_mode)
	{
		log_assert(aig_m == aig_i + aig_l + aig_a);
		log_assert(aig_l == GetSize(aig_latchin));
		log_assert(aig_l == GetSize(aig_latchinit));
		log_assert(aig_o == GetSize(aig_outputs));

		if (miter_mode)
			f << stringf("%s %d %d %d 0 %d %d\n", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l,  aig_a, aig_o);
		else
			f << stringf("%s %d %d %d %d %d\n", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l, aig_o, aig_a);

		if (ascii_mode)
		{
			for (int i = 0; i < aig_i; i++)
				f << stringf("%d\n", 2*i+2);

			for (int i = 0; i < aig_l; i++) {
				if (aig_latchinit.at(i) == 0)
					f << stringf("%d %d\n", 2*(aig_i+i)+2, aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 1)
					f << stringf("%d %d 1\n", 2*(aig_i+i)+2, aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 2)
					f << stringf("%d %d %d\n", 2*(aig_i+i)+2, aig_latchin.at(i), 2*(aig_i+i)+2);
			}

			for (int i = 0; i < aig_o; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = 0; i < aig_a; i++)
				f << stringf("%d %d %d\n", 2*(aig_i+aig_l+i)+2, aig_gates.at(i).first, aig_gates.at(i).second);
		}
		else
		{
			for (int i = 0; i < aig_l; i++) {
				if (aig_latchinit.at(i) == 0)
					f << stringf("%d\n", aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 1)
					f << stringf("%d 1\n", aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 2)
					f << stringf("%d %d\n", aig_latchin.at(i), 2*(aig_i+i)+2);
			}

			for (int i = 0; i < aig_o; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = 0; i < aig_a; i++) {
				int lhs = 2*(aig_i+aig_l+i)+2;
				int rhs0 = aig_gates.at(i).first;
				int rhs1 = aig_gates.at(i).second;
				int delta0 = lhs - rhs0;
				int delta1 = rhs0 - rhs1;
				aiger_encode(f, delta0);
				aiger_encode(f, delta1);
			}
		}

		f << stringf("c\nGenerated by %s\n", yosys_version_str);
	}

	void write_map(std::ostream &f)
	{
		dict<int, string> input_lines;
		dict<int, string> output_lines;
		dict<int, string> latch_lines;
		dict<int, string> wire_lines;

		for (auto wire : module->wires())
		{
			if (wire->name[0] == '$')
				continue;

			SigSpec sig = sigmap(wire);

			for (int i = 0; i < GetSize(wire); i++)
			{
				if (aig_map.count(sig[i]) == 0)
					continue;

				int a = aig_map.at(sig[i]);
				// wire_lines[a] = stringf("wire %d %d %s\n", a, i, log_id(wire));

				if (wire->port_input) {
					log_assert((a & 1) == 0);
					input_lines[a] = stringf("input %d %d %s\n", (a >> 1)-1, i, log_id(wire));
				}

				if (wire->port_output) {
					int n = ordered_outputs.at(sig[i]);
					output_lines[n] = stringf("output %d %d %s\n", n-1, i, log_id(wire));
				}

				if (ordered_latches.count(sig[i])) {
					int n = ordered_latches.at(sig[i]);
					latch_lines[n] = stringf("latch %d %d %s\n", n-1, i, log_id(wire));
				}
			}
		}

		input_lines.sort();
		for (auto &it : input_lines)
			f << it.second;

		output_lines.sort();
		for (auto &it : output_lines)
			f << it.second;

		latch_lines.sort();
		for (auto &it : latch_lines)
			f << it.second;

		wire_lines.sort();
		for (auto &it : wire_lines)
			f << it.second;
	}
};

struct AigerBackend : public Backend {
	AigerBackend() : Backend("aiger", "write design to AIGER file") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_aiger [options] [filename]\n");
		log("\n");
		log("Write the current design to an AIGER file. The design must be flattened and\n");
		log("must not contain any cell types except $_AND_, $_NOT_, and simple FF types.\n");
		log("\n");
		log("    -ascii\n");
		log("        write ASCII version of AGIER format\n");
		log("\n");
		// log("    -zinit\n");
		// log("        convert FFs to zero-initialized FFs, adding additional inputs for\n");
		// log("        uninitialized FFs.\n");
		// log("\n");
		log("    -miter\n");
		log("        design outputs are AIGER bad state properties\n");
		log("\n");
		log("    -map <filename>\n");
		log("        write an extra file with port, latch and wire mappings\n");
		log("\n");
	}
	virtual void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design)
	{
		bool ascii_mode = false;
		bool zinit_mode = false;
		bool miter_mode = false;
		std::string map_filename;

		log_header(design, "Executing AIGER backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-ascii") {
				ascii_mode = true;
				continue;
			}
			if (args[argidx] == "-zinit") {
				zinit_mode = true;
				continue;
			}
			if (args[argidx] == "-miter") {
				miter_mode = true;
				continue;
			}
			if (args[argidx] == "-map" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		Module *top_module = design->top_module();

		if (top_module == nullptr)
			log_error("Can't find top module in current design!\n");

		if (zinit_mode)
			log_error("zinit mode is not implemented yet.\n");

		AigerWriter writer(top_module, zinit_mode);
		writer.write_aiger(*f, ascii_mode, miter_mode);

		if (!map_filename.empty()) {
			std::ofstream mapf;
			mapf.open(map_filename.c_str(), std::ofstream::trunc);
			if (mapf.fail())
				log_error("Can't open file `%s' for writing: %s\n", map_filename.c_str(), strerror(errno));
			writer.write_map(mapf);
		}
	}
} AigerBackend;

PRIVATE_NAMESPACE_END
