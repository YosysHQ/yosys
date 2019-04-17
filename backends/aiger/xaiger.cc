/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *  Copyright (C) 2019  Eddie Hung <eddie@fpgeh.com>
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

struct XAigerWriter
{
	Module *module;
	bool zinit_mode;
	SigMap sigmap;

	dict<SigBit, bool> init_map;
	pool<SigBit> input_bits, output_bits;
	dict<SigBit, SigBit> not_map, ff_map, alias_map;
	dict<SigBit, pair<SigBit, SigBit>> and_map;
	pool<SigBit> initstate_bits;
	vector<std::pair<SigBit,int>> ci_bits, co_bits;
	dict<IdString, unsigned> type_map;

	vector<pair<int, int>> aig_gates;
	vector<int> aig_latchin, aig_latchinit, aig_outputs;
	int aig_m = 0, aig_i = 0, aig_l = 0, aig_o = 0, aig_a = 0;

	dict<SigBit, int> aig_map;
	dict<SigBit, int> ordered_outputs;
	dict<SigBit, int> ordered_latches;

	dict<SigBit, int> init_inputs;
	int initstate_ff = 0;

	vector<Cell*> box_list;

	int mkgate(int a0, int a1)
	{
		aig_m++, aig_a++;
		aig_gates.push_back(a0 > a1 ? make_pair(a0, a1) : make_pair(a1, a0));
		return 2*aig_m;
	}

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
				aig_map[bit] = mkgate(a0, a1);
			} else
			if (alias_map.count(bit)) {
				aig_map[bit] = bit2aig(alias_map.at(bit));
			}

			if (bit == State::Sx || bit == State::Sz)
				log_error("Design contains 'x' or 'z' bits. Use 'setundef' to replace those constants.\n");
		}

		log_assert(aig_map.at(bit) >= 0);
		return aig_map.at(bit);
	}

	XAigerWriter(Module *module, bool zinit_mode, bool imode, bool omode, bool bmode) : module(module), zinit_mode(zinit_mode), sigmap(module)
	{
		pool<SigBit> undriven_bits;
		pool<SigBit> unused_bits;

		// promote public wires
		for (auto wire : module->wires())
			if (wire->name[0] == '\\')
				sigmap.add(wire);

		// promote input wires
		for (auto wire : module->wires())
			if (wire->port_input)
				sigmap.add(wire);

		// promote output wires
		for (auto wire : module->wires())
			if (wire->port_output)
				sigmap.add(wire);

		for (auto wire : module->wires())
		{
			if (wire->attributes.count("\\init")) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at("\\init");
				for (int i = 0; i < GetSize(wire) && i < GetSize(initval); i++)
					if (initval[i] == State::S0 || initval[i] == State::S1)
						init_map[initsig[i]] = initval[i] == State::S1;
			}

			for (int i = 0; i < GetSize(wire); i++)
			{
				SigBit wirebit(wire, i);
				SigBit bit = sigmap(wirebit);

				if (bit.wire == nullptr) {
					if (wire->port_output) {
						aig_map[wirebit] = (bit == State::S1) ? 1 : 0;
						output_bits.insert(wirebit);
					}
					continue;
				}

				undriven_bits.insert(bit);
				unused_bits.insert(bit);

				if (wire->port_input)
					input_bits.insert(bit);

				if (wire->port_output) {
					if (bit != wirebit)
						alias_map[wirebit] = bit;
					output_bits.insert(wirebit);
				}
			}
		}

		for (auto bit : input_bits) {
			if (!bit.wire->port_output)
				undriven_bits.erase(bit);
			// Erase POs that are also PIs
			output_bits.erase(bit);
		}

		for (auto bit : output_bits)
			if (!bit.wire->port_input)
				unused_bits.erase(bit);

		for (auto cell : module->cells())
		{
			if (cell->type == "$_NOT_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				unused_bits.erase(A);
				undriven_bits.erase(Y);
				not_map[Y] = A;
				continue;
			}

			//if (cell->type.in("$_FF_", "$_DFF_N_", "$_DFF_P_"))
			//{
			//	SigBit D = sigmap(cell->getPort("\\D").as_bit());
			//	SigBit Q = sigmap(cell->getPort("\\Q").as_bit());
			//	unused_bits.erase(D);
			//	undriven_bits.erase(Q);
			//	ff_map[Q] = D;
			//	continue;
			//}

			if (cell->type == "$_AND_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit B = sigmap(cell->getPort("\\B").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				unused_bits.erase(A);
				unused_bits.erase(B);
				undriven_bits.erase(Y);
				and_map[Y] = make_pair(A, B);
				continue;
			}

			if (cell->type == "$initstate")
			{
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				undriven_bits.erase(Y);
				initstate_bits.insert(Y);
				continue;
			}

			RTLIL::Module* box_module = module->design->module(cell->type);
			bool abc_box = box_module && box_module->attributes.count("\\abc_box_id");

			cell->connections_.sort(RTLIL::sort_by_id_str());
			for (const auto &c : cell->connections()) {
				/*if (c.second.is_fully_const()) continue;*/
				for (auto b : c.second.bits()) {
					auto is_input = cell->input(c.first);
					auto is_output = cell->output(c.first);
					log_assert(is_input || is_output);
					if (is_input) {
						/*if (!w->port_input)*/ {
							SigBit I = sigmap(b);
							if (I != b)
								alias_map[b] = I;
							/*if (!output_bits.count(b))*/
							if (abc_box)
								co_bits.emplace_back(b, 0);
							else if (b.wire) {
								output_bits.insert(b);
								if (!b.wire->port_input)
									unused_bits.erase(b);
							}
						}
					}
					if (is_output) {
						SigBit O = sigmap(b);
						/*if (!input_bits.count(O))*/
						if (abc_box)
							ci_bits.emplace_back(O, 0);
						else {
							input_bits.insert(O);
							if (!O.wire->port_output)
								undriven_bits.erase(O);
						}
					}
				}
				if (!type_map.count(cell->type))
					type_map[cell->type] = type_map.size()+1;
			}

			if (abc_box)
				box_list.emplace_back(cell);
			//log_warning("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));
		}

		for (auto bit : input_bits) {
			RTLIL::Wire *wire = bit.wire;
			// If encountering an inout port, then create a new wire with $inout.out
			// suffix, make it a PO driven by the existing inout, and inherit existing
			// inout's drivers
			if (wire->port_input && wire->port_output && !undriven_bits.count(bit)) {
				RTLIL::Wire *new_wire = module->wire(wire->name.str() + "$inout.out");
				if (!new_wire)
					new_wire = module->addWire(wire->name.str() + "$inout.out", GetSize(wire));
				SigBit new_bit(new_wire, bit.offset);
				module->connect(new_bit, bit);
				if (not_map.count(bit))
					not_map[new_bit] = not_map.at(bit);
				else if (and_map.count(bit))
					and_map[new_bit] = and_map.at(bit);
				else if (alias_map.count(bit))
					alias_map[new_bit] = alias_map.at(bit);
				output_bits.insert(new_bit);
			}
		}

		// Do some CI/CO post-processing:
		// Erase all POs and COs that are undriven
		for (auto bit : undriven_bits) {
			//co_bits.erase(bit);
			output_bits.erase(bit);
		}
		// Erase all CIs that are also COs
		//for (auto bit : co_bits)
		//	ci_bits.erase(bit);
		// CIs cannot be undriven
		for (const auto &c : ci_bits)
			undriven_bits.erase(c.first);

		for (auto bit : unused_bits)
			undriven_bits.erase(bit);

		if (!undriven_bits.empty()) {
			undriven_bits.sort();
			for (auto bit : undriven_bits) {
				log_warning("Treating undriven bit %s.%s like $anyseq.\n", log_id(module), log_signal(bit));
				input_bits.insert(bit);
			}
			log_warning("Treating a total of %d undriven bits in %s like $anyseq.\n", GetSize(undriven_bits), log_id(module));
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

		for (auto &c : ci_bits) {
			aig_m++, aig_i++;
			c.second = 2*aig_m;
			aig_map[c.first] = c.second;
		}

		if (imode && input_bits.empty()) {
			aig_m++, aig_i++;
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
			ordered_latches[it.first] = aig_l-1;
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

		if (zinit_mode)
		{
			for (auto it : ff_map)
			{
				int l = ordered_latches[it.first];

				if (aig_latchinit.at(l) == 1)
					aig_map[it.first] ^= 1;

				if (aig_latchinit.at(l) == 2)
				{
					int gated_ffout = mkgate(aig_map[it.first], initstate_ff^1);
					int gated_initin = mkgate(init_inputs[it.first], initstate_ff);
					aig_map[it.first] = mkgate(gated_ffout^1, gated_initin^1)^1;
				}
			}
		}

		for (auto it : ff_map) {
			int a = bit2aig(it.second);
			int l = ordered_latches[it.first];
			if (zinit_mode && aig_latchinit.at(l) == 1)
				aig_latchin.push_back(a ^ 1);
			else
				aig_latchin.push_back(a);
		}

		if (!initstate_bits.empty() || !init_inputs.empty())
			aig_latchin.push_back(1);

		for (auto &c : co_bits) {
			RTLIL::SigBit bit = c.first;
			c.second = aig_o++;
			ordered_outputs[bit] = c.second;
			aig_outputs.push_back(bit2aig(bit));
		}

		for (auto bit : output_bits) {
			ordered_outputs[bit] = aig_o++;
			aig_outputs.push_back(bit2aig(bit));
		}

		if (omode && output_bits.empty()) {
			aig_o++;
			aig_outputs.push_back(0);
		}

		if (bmode) {
			//aig_b++;
			aig_outputs.push_back(0);
		}
	}

	void write_aiger(std::ostream &f, bool ascii_mode, bool miter_mode, bool symbols_mode, bool omode)
	{
		int aig_obc = aig_o;
		int aig_obcj = aig_obc;
		int aig_obcjf = aig_obcj;

		log_assert(aig_m == aig_i + aig_l + aig_a);
		log_assert(aig_l == GetSize(aig_latchin));
		log_assert(aig_l == GetSize(aig_latchinit));
		log_assert(aig_obcjf == GetSize(aig_outputs));

		f << stringf("%s %d %d %d %d %d", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l, aig_o, aig_a);
		f << stringf("\n");

		if (ascii_mode)
		{
			for (int i = 0; i < aig_i; i++)
				f << stringf("%d\n", 2*i+2);

			for (int i = 0; i < aig_l; i++) {
				if (zinit_mode || aig_latchinit.at(i) == 0)
					f << stringf("%d %d\n", 2*(aig_i+i)+2, aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 1)
					f << stringf("%d %d 1\n", 2*(aig_i+i)+2, aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 2)
					f << stringf("%d %d %d\n", 2*(aig_i+i)+2, aig_latchin.at(i), 2*(aig_i+i)+2);
			}

			for (int i = 0; i < aig_obc; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = aig_obc; i < aig_obcj; i++)
				f << stringf("1\n");

			for (int i = aig_obc; i < aig_obcj; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = aig_obcj; i < aig_obcjf; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = 0; i < aig_a; i++)
				f << stringf("%d %d %d\n", 2*(aig_i+aig_l+i)+2, aig_gates.at(i).first, aig_gates.at(i).second);
		}
		else
		{
			for (int i = 0; i < aig_l; i++) {
				if (zinit_mode || aig_latchinit.at(i) == 0)
					f << stringf("%d\n", aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 1)
					f << stringf("%d 1\n", aig_latchin.at(i));
				else if (aig_latchinit.at(i) == 2)
					f << stringf("%d %d\n", aig_latchin.at(i), 2*(aig_i+i)+2);
			}

			for (int i = 0; i < aig_obc; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = aig_obc; i < aig_obcj; i++)
				f << stringf("1\n");

			for (int i = aig_obc; i < aig_obcj; i++)
				f << stringf("%d\n", aig_outputs.at(i));

			for (int i = aig_obcj; i < aig_obcjf; i++)
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

		if (symbols_mode)
		{
			dict<string, vector<string>> symbols;

			bool output_seen = false;
			for (auto wire : module->wires())
			{
				//if (wire->name[0] == '$')
				//	continue;

				SigSpec sig = sigmap(wire);

				for (int i = 0; i < GetSize(wire); i++)
				{
					RTLIL::SigBit b(wire, i);
					if (input_bits.count(b)) {
						int a = aig_map.at(sig[i]);
						log_assert((a & 1) == 0);
						if (GetSize(wire) != 1)
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("%s[%d]", log_id(wire), i));
						else
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("%s", log_id(wire)));
					}

					if (output_bits.count(b)) {
						int o = ordered_outputs.at(b);
						output_seen = !miter_mode;
						if (GetSize(wire) != 1)
							symbols[stringf("%c%d", miter_mode ? 'b' : 'o', o)].push_back(stringf("%s[%d]", log_id(wire), i));
						else
							symbols[stringf("%c%d", miter_mode ? 'b' : 'o', o)].push_back(stringf("%s", log_id(wire)));
					}

					if (init_inputs.count(sig[i])) {
						int a = init_inputs.at(sig[i]);
						log_assert((a & 1) == 0);
						if (GetSize(wire) != 1)
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("init:%s[%d]", log_id(wire), i));
						else
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("init:%s", log_id(wire)));
					}

					if (ordered_latches.count(sig[i])) {
						int l = ordered_latches.at(sig[i]);
						const char *p = (zinit_mode && (aig_latchinit.at(l) == 1)) ? "!" : "";
						if (GetSize(wire) != 1)
							symbols[stringf("l%d", l)].push_back(stringf("%s%s[%d]", p, log_id(wire), i));
						else
							symbols[stringf("l%d", l)].push_back(stringf("%s%s", p, log_id(wire)));
					}
				}
			}

			if (omode && !output_seen)
				symbols["o0"].push_back("__dummy_o__");

			symbols.sort();

			for (auto &sym : symbols) {
				f << sym.first;
				std::sort(sym.second.begin(), sym.second.end());
				for (auto &s : sym.second)
					f << " " << s;
				f << std::endl;
			}
		}

		f << "c";

		if (!box_list.empty()) {
			std::stringstream h_buffer;
			auto write_h_buffer = [&h_buffer](int i32) {
				// TODO: Don't assume we're on little endian
#ifdef _WIN32
				int i32_be = _byteswap_ulong(i32);
#else
				int i32_be = __builtin_bswap32(i32);
#endif
				h_buffer.write(reinterpret_cast<const char*>(&i32_be), sizeof(i32_be));
			};
			int num_outputs = output_bits.size();
			if (omode && num_outputs == 0)
				num_outputs = 1;
			write_h_buffer(1);
			write_h_buffer(input_bits.size() + ci_bits.size());
			write_h_buffer(num_outputs + co_bits.size());
			write_h_buffer(input_bits.size());
			write_h_buffer(num_outputs);
			write_h_buffer(box_list.size());

			RTLIL::Module *holes_module = nullptr;
			holes_module = module->design->addModule("\\__holes__");

			for (auto cell : box_list) {
				int box_inputs = 0, box_outputs = 0;
				int box_id = module->design->module(cell->type)->attributes.at("\\abc_box_id").as_int();
				Cell *holes_cell = nullptr;
				if (holes_module && !holes_module->cell(stringf("\\u%d", box_id)))
					holes_cell = holes_module->addCell(stringf("\\u%d", box_id), cell->type);
				RTLIL::Wire *holes_wire;
				// NB: cell->connections_ already sorted from before
				for (const auto &c : cell->connections()) {
					log_assert(c.second.size() == 1);
					if (cell->input(c.first)) {
						box_inputs += c.second.size();
						if (holes_cell) {
							holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
							if (!holes_wire) {
								holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
								holes_wire->port_input = true;
							}
							holes_cell->setPort(c.first, holes_wire);
						}
					}
					if (cell->output(c.first)) {
						box_outputs += c.second.size();
						if (holes_cell) {
							holes_wire = holes_module->addWire(stringf("\\%s.%s", cell->type.c_str(), c.first.c_str()));
							holes_wire->port_output = true;
							holes_cell->setPort(c.first, holes_wire);
						}
					}
				}
				write_h_buffer(box_inputs);
				write_h_buffer(box_outputs);
				write_h_buffer(box_id);
				write_h_buffer(0 /* OldBoxNum */);
			}

			f << "h";
			std::string buffer_str = h_buffer.str();
			// TODO: Don't assume we're on little endian
#ifdef _WIN32
			int buffer_size_be = _byteswap_ulong(buffer_str.size());
#else
			int buffer_size_be = __builtin_bswap32(buffer_str.size());
#endif
			f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
			f.write(buffer_str.data(), buffer_str.size());

			if (holes_module) {
				holes_module->fixup_ports();

				holes_module->design->selection_stack.emplace_back(false);
				RTLIL::Selection& sel = holes_module->design->selection_stack.back();
				sel.select(holes_module);

				Pass::call(holes_module->design, "flatten; aigmap");

				holes_module->design->selection_stack.pop_back();

				std::stringstream a_buffer;
				XAigerWriter writer(holes_module, false /*zinit_mode*/, false /*imode*/, false /*omode*/, false /*bmode*/);
				writer.write_aiger(a_buffer, false /*ascii_mode*/, false /*miter_mode*/, false /*symbols_mode*/, false /*omode*/);

				f << "a";
				std::string buffer_str = a_buffer.str();
				// TODO: Don't assume we're on little endian
#ifdef _WIN32
				int buffer_size_be = _byteswap_ulong(buffer_str.size());
#else
				int buffer_size_be = __builtin_bswap32(buffer_str.size());
#endif
				f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
				f.write(buffer_str.data(), buffer_str.size());
				holes_module->design->remove(holes_module);
			}
		}

		f << stringf("Generated by %s\n", yosys_version_str);
	}

	void write_map(std::ostream &f, bool verbose_map, bool omode)
	{
		dict<int, string> input_lines;
		dict<int, string> init_lines;
		dict<int, string> output_lines;
		dict<int, string> latch_lines;
		dict<int, string> wire_lines;

		for (auto wire : module->wires())
		{
			//if (!verbose_map && wire->name[0] == '$')
			//	continue;

			SigSpec sig = sigmap(wire);

			for (int i = 0; i < GetSize(wire); i++)
			{
				RTLIL::SigBit b(wire, i);
				if (input_bits.count(b)) {
					int a = aig_map.at(sig[i]);
					log_assert((a & 1) == 0);
					input_lines[a] += stringf("input %d %d %s\n", (a >> 1)-1, i, log_id(wire));
				}

				if (output_bits.count(b)) {
					int o = ordered_outputs.at(b);
					output_lines[o] += stringf("output %d %d %s\n", o, i, log_id(wire));
					continue;
				}

				if (init_inputs.count(sig[i])) {
					int a = init_inputs.at(sig[i]);
					log_assert((a & 1) == 0);
					init_lines[a] += stringf("init %d %d %s\n", (a >> 1)-1, i, log_id(wire));
					continue;
				}

				if (ordered_latches.count(sig[i])) {
					int l = ordered_latches.at(sig[i]);
					if (zinit_mode && (aig_latchinit.at(l) == 1))
						latch_lines[l] += stringf("invlatch %d %d %s\n", l, i, log_id(wire));
					else
						latch_lines[l] += stringf("latch %d %d %s\n", l, i, log_id(wire));
					continue;
				}

				if (verbose_map) {
					if (aig_map.count(sig[i]) == 0)
						continue;

					int a = aig_map.at(sig[i]);
					wire_lines[a] += stringf("wire %d %d %s\n", a, i, log_id(wire));
				}
			}
		}

		for (const auto &c : ci_bits) {
			RTLIL::SigBit b = c.first;
			RTLIL::Wire *wire = b.wire;
			int i = b.offset;
			int a = c.second;
			log_assert((a & 1) == 0);
			input_lines[a] += stringf("input %d %d %s\n", (a >> 1)-1, i, log_id(wire));
		}

		for (const auto &c : co_bits) {
			RTLIL::SigBit b = c.first;
			RTLIL::Wire *wire = b.wire;
			int o = c.second;
			if (wire)
				output_lines[o] += stringf("output %d %d %s\n", o, b.offset, log_id(wire));
			else
				output_lines[o] += stringf("output %d %d __const%d__\n", o, 0, b.data);
		}

		input_lines.sort();
		for (auto &it : input_lines)
			f << it.second;
		log_assert(input_lines.size() == input_bits.size() + ci_bits.size());

		init_lines.sort();
		for (auto &it : init_lines)
			f << it.second;

		output_lines.sort();
		for (auto &it : output_lines)
			f << it.second;
		log_assert(output_lines.size() == output_bits.size() + co_bits.size());
		if (omode && output_bits.empty())
			f << "output " << output_lines.size() << " 0 __dummy_o__\n";

		latch_lines.sort();
		for (auto &it : latch_lines)
			f << it.second;

		wire_lines.sort();
		for (auto &it : wire_lines)
			f << it.second;
	}
};

struct XAigerBackend : public Backend {
	XAigerBackend() : Backend("xaiger", "write design to XAIGER file") { }
	void help() YS_OVERRIDE
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_xaiger [options] [filename]\n");
		log("\n");
		log("Write the current design to an XAIGER file. The design must be flattened and\n");
		log("all unsupported cells will be converted into psuedo-inputs and pseudo-outputs.\n");
		log("\n");
		log("    -ascii\n");
		log("        write ASCII version of AGIER format\n");
		log("\n");
		log("    -zinit\n");
		log("        convert FFs to zero-initialized FFs, adding additional inputs for\n");
		log("        uninitialized FFs.\n");
		log("\n");
		log("    -symbols\n");
		log("        include a symbol table in the generated AIGER file\n");
		log("\n");
		log("    -map <filename>\n");
		log("        write an extra file with port and latch symbols\n");
		log("\n");
		log("    -vmap <filename>\n");
		log("        like -map, but more verbose\n");
		log("\n");
		log("    -I, -O, -B\n");
		log("        If the design contains no input/output/assert then create one\n");
		log("        dummy input/output/bad_state pin to make the tools reading the\n");
		log("        AIGER file happy.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool ascii_mode = false;
		bool zinit_mode = false;
		bool miter_mode = false;
		bool symbols_mode = false;
		bool verbose_map = false;
		bool imode = false;
		bool omode = false;
		bool bmode = false;
		std::string map_filename;

		log_header(design, "Executing XAIGER backend.\n");

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
			if (args[argidx] == "-symbols") {
				symbols_mode = true;
				continue;
			}
			if (map_filename.empty() && args[argidx] == "-map" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
			if (map_filename.empty() && args[argidx] == "-vmap" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				verbose_map = true;
				continue;
			}
			if (args[argidx] == "-I") {
				imode = true;
				continue;
			}
			if (args[argidx] == "-O") {
				omode = true;
				continue;
			}
			if (args[argidx] == "-B") {
				bmode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		Module *top_module = design->top_module();

		if (top_module == nullptr)
			log_error("Can't find top module in current design!\n");

		XAigerWriter writer(top_module, zinit_mode, imode, omode, bmode);
		writer.write_aiger(*f, ascii_mode, miter_mode, symbols_mode, omode);

		if (!map_filename.empty()) {
			std::ofstream mapf;
			mapf.open(map_filename.c_str(), std::ofstream::trunc);
			if (mapf.fail())
				log_error("Can't open file `%s' for writing: %s\n", map_filename.c_str(), strerror(errno));
			writer.write_map(mapf, verbose_map, omode);
		}
	}
} XAigerBackend;

PRIVATE_NAMESPACE_END
