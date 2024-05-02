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
#include "kernel/json.h"
#include "kernel/yw.h"
#include "libs/json11/json11.hpp"

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
	dict<SigBit, SigBit> not_map, ff_map, alias_map;
	dict<SigBit, pair<SigBit, SigBit>> and_map;
	vector<pair<SigBit, SigBit>> asserts, assumes;
	vector<pair<SigBit, SigBit>> liveness, fairness;
	pool<SigBit> initstate_bits;

	vector<pair<int, int>> aig_gates;
	vector<int> aig_latchin, aig_latchinit, aig_outputs;
	vector<SigBit> bit2aig_stack;
	size_t next_loop_check = 1024;
	int aig_m = 0, aig_i = 0, aig_l = 0, aig_o = 0, aig_a = 0;
	int aig_b = 0, aig_c = 0, aig_j = 0, aig_f = 0;

	dict<SigBit, int> aig_map;
	dict<SigBit, int> ordered_outputs;
	dict<SigBit, int> ordered_latches;

	dict<SigBit, int> init_inputs;
	int initstate_ff = 0;

	dict<SigBit, int> ywmap_clocks;
	vector<Cell *> ywmap_asserts;
	vector<Cell *> ywmap_assumes;

	int mkgate(int a0, int a1)
	{
		aig_m++, aig_a++;
		aig_gates.push_back(a0 > a1 ? make_pair(a0, a1) : make_pair(a1, a0));
		return 2*aig_m;
	}

	int bit2aig(SigBit bit)
	{
		auto it = aig_map.find(bit);
		if (it != aig_map.end()) {
			log_assert(it->second >= 0);
			return it->second;
		}

		if (bit2aig_stack.size() == next_loop_check) {
			for (size_t i = 0; i < next_loop_check; ++i)
			{
				SigBit report_bit = bit2aig_stack[i];
				if (report_bit != bit)
					continue;
				for (size_t j = i; j < next_loop_check; ++j) {
					report_bit = bit2aig_stack[j];
					if (report_bit.is_wire() && report_bit.wire->name.isPublic())
						break;
				}
				log_error("Found combinational logic loop while processing signal %s.\n", log_signal(report_bit));
			}
			next_loop_check *= 2;
		}
		bit2aig_stack.push_back(bit);

		// NB: Cannot use iterator returned from aig_map.insert()
		//     since this function is called recursively

		int a = -1;
		if (not_map.count(bit)) {
			a = bit2aig(not_map.at(bit)) ^ 1;
		} else
		if (and_map.count(bit)) {
			auto args = and_map.at(bit);
			int a0 = bit2aig(args.first);
			int a1 = bit2aig(args.second);
			a = mkgate(a0, a1);
		} else
		if (alias_map.count(bit)) {
			a = bit2aig(alias_map.at(bit));
		} else
		if (initstate_bits.count(bit)) {
			a = initstate_ff;
		}

		bit2aig_stack.pop_back();

		if (bit == State::Sx || bit == State::Sz)
			log_error("Design contains 'x' or 'z' bits. Use 'setundef' to replace those constants.\n");

		log_assert(a >= 0);
		aig_map[bit] = a;
		return a;
	}

	AigerWriter(Module *module, bool zinit_mode, bool imode, bool omode, bool bmode, bool lmode) : module(module), zinit_mode(zinit_mode), sigmap(module)
	{
		pool<SigBit> undriven_bits;
		pool<SigBit> unused_bits;

		// promote public wires
		for (auto wire : module->wires())
			if (wire->name.isPublic())
				sigmap.add(wire);

		// promote output wires
		for (auto wire : module->wires())
			if (wire->port_output)
				sigmap.add(wire);

		// promote input wires
		for (auto wire : module->wires())
			if (wire->port_input)
				sigmap.add(wire);

		for (auto wire : module->wires())
		{
			if (wire->attributes.count(ID::init)) {
				SigSpec initsig = sigmap(wire);
				Const initval = wire->attributes.at(ID::init);
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

			if (wire->width == 1) {
				auto gclk_attr = wire->attributes.find(ID::replaced_by_gclk);
				if (gclk_attr != wire->attributes.end()) {
					SigBit bit = sigmap(wire);
					if (gclk_attr->second == State::S1)
						ywmap_clocks[bit] |= 1;
					else if (gclk_attr->second == State::S0)
						ywmap_clocks[bit] |= 2;
				}
			}
		}

		for (auto bit : input_bits)
			undriven_bits.erase(bit);

		for (auto bit : output_bits)
			unused_bits.erase(bit);

		for (auto cell : module->cells())
		{
			if (cell->type == ID($_NOT_))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit Y = sigmap(cell->getPort(ID::Y).as_bit());
				unused_bits.erase(A);
				undriven_bits.erase(Y);
				not_map[Y] = A;
				continue;
			}

			if (cell->type.in(ID($_FF_), ID($_DFF_N_), ID($_DFF_P_)))
			{
				SigBit D = sigmap(cell->getPort(ID::D).as_bit());
				SigBit Q = sigmap(cell->getPort(ID::Q).as_bit());
				unused_bits.erase(D);
				undriven_bits.erase(Q);
				ff_map[Q] = D;

				if (cell->type != ID($_FF_)) {
					auto sig_clk = sigmap(cell->getPort(ID::C).as_bit());
					ywmap_clocks[sig_clk] |= cell->type == ID($_DFF_N_) ? 2 : 1;
				}
				continue;
			}

			if (cell->type == ID($anyinit))
			{
				auto sig_d = sigmap(cell->getPort(ID::D));
				auto sig_q = sigmap(cell->getPort(ID::Q));
				for (int i = 0; i < sig_d.size(); i++) {
					undriven_bits.erase(sig_q[i]);
					ff_map[sig_q[i]] = sig_d[i];
				}
				continue;
			}

			if (cell->type == ID($_AND_))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit B = sigmap(cell->getPort(ID::B).as_bit());
				SigBit Y = sigmap(cell->getPort(ID::Y).as_bit());
				unused_bits.erase(A);
				unused_bits.erase(B);
				undriven_bits.erase(Y);
				and_map[Y] = make_pair(A, B);
				continue;
			}

			if (cell->type == ID($initstate))
			{
				SigBit Y = sigmap(cell->getPort(ID::Y).as_bit());
				undriven_bits.erase(Y);
				initstate_bits.insert(Y);
				continue;
			}

			if (cell->type == ID($assert))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit EN = sigmap(cell->getPort(ID::EN).as_bit());
				unused_bits.erase(A);
				unused_bits.erase(EN);
				asserts.push_back(make_pair(A, EN));
				ywmap_asserts.push_back(cell);
				continue;
			}

			if (cell->type == ID($assume))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit EN = sigmap(cell->getPort(ID::EN).as_bit());
				unused_bits.erase(A);
				unused_bits.erase(EN);
				assumes.push_back(make_pair(A, EN));
				ywmap_assumes.push_back(cell);
				continue;
			}

			if (cell->type == ID($live))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit EN = sigmap(cell->getPort(ID::EN).as_bit());
				unused_bits.erase(A);
				unused_bits.erase(EN);
				liveness.push_back(make_pair(A, EN));
				continue;
			}

			if (cell->type == ID($fair))
			{
				SigBit A = sigmap(cell->getPort(ID::A).as_bit());
				SigBit EN = sigmap(cell->getPort(ID::EN).as_bit());
				unused_bits.erase(A);
				unused_bits.erase(EN);
				fairness.push_back(make_pair(A, EN));
				continue;
			}

			if (cell->type == ID($anyconst))
			{
				for (auto bit : sigmap(cell->getPort(ID::Y))) {
					undriven_bits.erase(bit);
					ff_map[bit] = bit;
				}
				continue;
			}

			if (cell->type == ID($anyseq))
			{
				for (auto bit : sigmap(cell->getPort(ID::Y))) {
					undriven_bits.erase(bit);
					input_bits.insert(bit);
				}
				continue;
			}

			if (cell->type == ID($scopeinfo))
				continue;

			log_error("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));
		}

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

		int fair_live_inputs_cnt = GetSize(liveness);
		int fair_live_inputs_m = aig_m;

		aig_m += fair_live_inputs_cnt;
		aig_i += fair_live_inputs_cnt;

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

		int fair_live_latches_cnt = GetSize(fairness) + 2*GetSize(liveness);
		int fair_live_latches_m = aig_m;
		int fair_live_latches_l = aig_l;

		aig_m += fair_live_latches_cnt;
		aig_l += fair_live_latches_cnt;

		for (int i = 0; i < fair_live_latches_cnt; i++)
			aig_latchinit.push_back(0);

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

		if (lmode && aig_l == 0) {
			aig_m++, aig_l++;
			aig_latchinit.push_back(0);
			aig_latchin.push_back(0);
		}

		if (!initstate_bits.empty() || !init_inputs.empty())
			aig_latchin.push_back(1);

		for (auto bit : output_bits) {
			aig_o++;
			ordered_outputs[bit] = aig_o-1;
			aig_outputs.push_back(bit2aig(bit));
		}

		if (omode && output_bits.empty()) {
			aig_o++;
			aig_outputs.push_back(0);
		}

		for (auto it : asserts) {
			aig_b++;
			int bit_a = bit2aig(it.first);
			int bit_en = bit2aig(it.second);
			aig_outputs.push_back(mkgate(bit_a^1, bit_en));
		}

		if (bmode && asserts.empty()) {
			aig_b++;
			aig_outputs.push_back(0);
		}

		for (auto it : assumes) {
			aig_c++;
			int bit_a = bit2aig(it.first);
			int bit_en = bit2aig(it.second);
			aig_outputs.push_back(mkgate(bit_a^1, bit_en)^1);
		}

		for (auto it : liveness)
		{
			int input_m = ++fair_live_inputs_m;
			int latch_m1 = ++fair_live_latches_m;
			int latch_m2 = ++fair_live_latches_m;

			log_assert(GetSize(aig_latchin) == fair_live_latches_l);
			fair_live_latches_l += 2;

			int bit_a = bit2aig(it.first);
			int bit_en = bit2aig(it.second);
			int bit_s = 2*input_m;
			int bit_q1 = 2*latch_m1;
			int bit_q2 = 2*latch_m2;

			int bit_d1 = mkgate(mkgate(bit_s, bit_en)^1, bit_q1^1)^1;
			int bit_d2 = mkgate(mkgate(bit_d1, bit_a)^1, bit_q2^1)^1;

			aig_j++;
			aig_latchin.push_back(bit_d1);
			aig_latchin.push_back(bit_d2);
			aig_outputs.push_back(mkgate(bit_q1, bit_q2^1));
		}

		for (auto it : fairness)
		{
			int latch_m = ++fair_live_latches_m;

			log_assert(GetSize(aig_latchin) == fair_live_latches_l);
			fair_live_latches_l += 1;

			int bit_a = bit2aig(it.first);
			int bit_en = bit2aig(it.second);
			int bit_q = 2*latch_m;

			aig_f++;
			aig_latchin.push_back(mkgate(mkgate(bit_q^1, bit_en^1)^1, bit_a^1));
			aig_outputs.push_back(bit_q^1);
		}
	}

	void write_aiger(std::ostream &f, bool ascii_mode, bool miter_mode, bool symbols_mode)
	{
		int aig_obc = aig_o + aig_b + aig_c;
		int aig_obcj = aig_obc + aig_j;
		int aig_obcjf = aig_obcj + aig_f;

		log_assert(aig_m == aig_i + aig_l + aig_a);
		log_assert(aig_l == GetSize(aig_latchin));
		log_assert(aig_l == GetSize(aig_latchinit));
		log_assert(aig_obcjf == GetSize(aig_outputs));

		if (miter_mode) {
			if (aig_b || aig_c || aig_j || aig_f)
				log_error("Running AIGER back-end in -miter mode, but design contains $assert, $assume, $live and/or $fair cells!\n");
			f << stringf("%s %d %d %d 0 %d %d\n", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l, aig_a, aig_o);
		} else {
			f << stringf("%s %d %d %d %d %d", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l, aig_o, aig_a);
			if (aig_b || aig_c || aig_j || aig_f)
				f << stringf(" %d %d %d %d", aig_b, aig_c, aig_j, aig_f);
			f << stringf("\n");
		}

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

			for (auto wire : module->wires())
			{
				if (wire->name[0] == '$')
					continue;

				SigSpec sig = sigmap(wire);

				for (int i = 0; i < GetSize(wire); i++)
				{
					if (sig[i].wire == nullptr) {
						if (wire->port_output)
							sig[i] = SigBit(wire, i);
						else
							continue;
					}

					if (wire->port_input) {
						int a = aig_map.at(sig[i]);
						log_assert((a & 1) == 0);
						if (GetSize(wire) != 1)
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("%s[%d]", log_id(wire), i));
						else
							symbols[stringf("i%d", (a >> 1)-1)].push_back(stringf("%s", log_id(wire)));
					}

					if (wire->port_output) {
						int o = ordered_outputs.at(SigSpec(wire, i));
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

			symbols.sort();

			for (auto &sym : symbols) {
				f << sym.first;
				std::sort(sym.second.begin(), sym.second.end());
				for (auto &s : sym.second)
					f << " " << s;
				f << std::endl;
			}
		}

		f << stringf("c\nGenerated by %s\n", yosys_version_str);
	}

	void write_map(std::ostream &f, bool verbose_map, bool no_startoffset)
	{
		dict<int, string> input_lines;
		dict<int, string> init_lines;
		dict<int, string> output_lines;
		dict<int, string> latch_lines;
		dict<int, string> wire_lines;

		for (auto wire : module->wires())
		{
			if (!verbose_map && wire->name[0] == '$')
				continue;

			SigSpec sig = sigmap(wire);

			for (int i = 0; i < GetSize(wire); i++)
			{
				if (aig_map.count(sig[i]) == 0 || sig[i].wire == nullptr)
					continue;

				int a = aig_map.at(sig[i]);
				int index = no_startoffset ? i : (wire->start_offset+i);

				if (verbose_map)
					wire_lines[a] += stringf("wire %d %d %s\n", a, index, log_id(wire));

				if (wire->port_input) {
					log_assert((a & 1) == 0);
					input_lines[a] += stringf("input %d %d %s\n", (a >> 1)-1, index, log_id(wire));
				}

				if (wire->port_output) {
					int o = ordered_outputs.at(sig[i]);
					output_lines[o] += stringf("output %d %d %s\n", o, index, log_id(wire));
				}

				if (init_inputs.count(sig[i])) {
					int a = init_inputs.at(sig[i]);
					log_assert((a & 1) == 0);
					init_lines[a] += stringf("init %d %d %s\n", (a >> 1)-1, index, log_id(wire));
				}

				if (ordered_latches.count(sig[i])) {
					int l = ordered_latches.at(sig[i]);
					if (zinit_mode && (aig_latchinit.at(l) == 1))
						latch_lines[l] += stringf("invlatch %d %d %s\n", l, index, log_id(wire));
					else
						latch_lines[l] += stringf("latch %d %d %s\n", l, index, log_id(wire));
				}
			}
		}

		input_lines.sort();
		for (auto &it : input_lines)
			f << it.second;

		init_lines.sort();
		for (auto &it : init_lines)
			f << it.second;

		output_lines.sort();
		for (auto &it : output_lines)
			f << it.second;

		latch_lines.sort();
		for (auto &it : latch_lines)
			f << it.second;

		if (initstate_ff)
			f << stringf("ninitff %d\n", ((initstate_ff >> 1)-1-aig_i));

		wire_lines.sort();
		for (auto &it : wire_lines)
			f << it.second;
	}

	void write_ywmap(PrettyJson &json)
	{
		json.begin_object();
		json.entry("version", "Yosys Witness Aiger map");
		json.entry("gennerator", yosys_version_str);

		json.entry("latch_count", aig_l);
		json.entry("input_count", aig_i);

		dict<int, Json> clock_lines;
		dict<int, Json> input_lines;
		dict<int, Json> init_lines;
		dict<int, Json> seq_lines;

		for (auto cell : module->cells())
		{
			if (cell->type.in(ID($_FF_), ID($_DFF_N_), ID($_DFF_P_), ID($anyinit), ID($anyconst), ID($anyseq)))
			{
				// Use sig_q to get the FF output name, but sig to lookup aiger bits
				auto sig_qy = cell->getPort(cell->type.in(ID($anyconst), ID($anyseq)) ? ID::Y : ID::Q);
				SigSpec sig = sigmap(sig_qy);

				if (cell->get_bool_attribute(ID(clk2fflogic)))
					sig_qy = cell->getPort(ID::D); // For a clk2fflogic $_FF_ the named signal is the D input not the Q output

				for (int i = 0; i < GetSize(sig_qy); i++) {
					if (sig_qy[i].wire == nullptr || sig[i].wire == nullptr)
						continue;

					auto wire = sig_qy[i].wire;

					if (init_inputs.count(sig[i])) {
						int a = init_inputs.at(sig[i]);
						log_assert((a & 1) == 0);
						init_lines[a] = json11::Json(json11::Json::object {
							{ "path", witness_path(wire) },
							{ "input", (a >> 1) - 1 },
							{ "offset", sig_qy[i].offset },
						});
					}

					if (input_bits.count(sig[i])) {
						int a = aig_map.at(sig[i]);
						log_assert((a & 1) == 0);
						seq_lines[a] = json11::Json(json11::Json::object {
							{ "path", witness_path(wire) },
							{ "input", (a >> 1) - 1 },
							{ "offset", sig_qy[i].offset },
						});
					}
				}
			}
		}

		for (auto wire : module->wires())
		{
			SigSpec sig = sigmap(wire);
			if (wire->port_input)
			{
				auto path = witness_path(wire);
				for (int i = 0; i < GetSize(wire); i++) {
					if (aig_map.count(sig[i]) == 0 || sig[i].wire == nullptr)
						continue;

					int a = aig_map.at(sig[i]);
					log_assert((a & 1) == 0);
					input_lines[a] = json11::Json(json11::Json::object {
						{ "path", path },
						{ "input", (a >> 1) - 1 },
						{ "offset", i },
					});

					if (ywmap_clocks.count(sig[i])) {
						int clock_mode = ywmap_clocks[sig[i]];
						if (clock_mode != 3) {
							clock_lines[a] = json11::Json(json11::Json::object {
								{ "path", path },
								{ "input", (a >> 1) - 1 },
								{ "offset", i },
								{ "edge", clock_mode == 1 ? "posedge" : "negedge" },
							});
						}
					}
				}
			}
		}

		json.name("clocks");
		json.begin_array();
		clock_lines.sort();
		for (auto &it : clock_lines)
			json.value(it.second);
		json.end_array();

		json.name("inputs");
		json.begin_array();
		input_lines.sort();
		for (auto &it : input_lines)
			json.value(it.second);
		json.end_array();

		json.name("seqs");
		json.begin_array();
		input_lines.sort();
		for (auto &it : seq_lines)
			json.value(it.second);
		json.end_array();

		json.name("inits");
		json.begin_array();
		input_lines.sort();
		for (auto &it : init_lines)
			json.value(it.second);
		json.end_array();

		json.name("asserts");
		json.begin_array();
		for (Cell *cell : ywmap_asserts)
			json.value(witness_path(cell));
		json.end_array();

		json.name("assumes");
		json.begin_array();
		for (Cell *cell : ywmap_assumes)
			json.value(witness_path(cell));
		json.end_array();

		json.end_object();
	}

};

struct AigerBackend : public Backend {
	AigerBackend() : Backend("aiger", "write design to AIGER file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_aiger [options] [filename]\n");
		log("\n");
		log("Write the current design to an AIGER file. The design must be flattened and\n");
		log("must not contain any cell types except $_AND_, $_NOT_, simple FF types,\n");
		log("$assert and $assume cells, and $initstate cells.\n");
		log("\n");
		log("$assert and $assume cells are converted to AIGER bad state properties and\n");
		log("invariant constraints.\n");
		log("\n");
		log("    -ascii\n");
		log("        write ASCII version of AIGER format\n");
		log("\n");
		log("    -zinit\n");
		log("        convert FFs to zero-initialized FFs, adding additional inputs for\n");
		log("        uninitialized FFs.\n");
		log("\n");
		log("    -miter\n");
		log("        design outputs are AIGER bad state properties\n");
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
		log("    -no-startoffset\n");
		log("        make indexes zero based, enable using map files with smt solvers.\n");
		log("\n");
		log("    -ywmap <filename>\n");
		log("        write a map file for conversion to and from yosys witness traces.\n");
		log("\n");
		log("    -I, -O, -B, -L\n");
		log("        If the design contains no input/output/assert/flip-flop then create one\n");
		log("        dummy input/output/bad_state-pin or latch to make the tools reading the\n");
		log("        AIGER file happy.\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool ascii_mode = false;
		bool zinit_mode = false;
		bool miter_mode = false;
		bool symbols_mode = false;
		bool verbose_map = false;
		bool imode = false;
		bool omode = false;
		bool bmode = false;
		bool lmode = false;
		bool no_startoffset = false;
		std::string map_filename;
		std::string yw_map_filename;

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
			if (yw_map_filename.empty() && args[argidx] == "-ywmap" && argidx+1 < args.size()) {
				yw_map_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-no-startoffset") {
				no_startoffset = true;
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
			if (args[argidx] == "-L") {
				lmode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx, !ascii_mode);

		if (!yw_map_filename.empty() && !zinit_mode)
			log_error("Currently -ywmap requires -zinit.\n");

		Module *top_module = design->top_module();

		if (top_module == nullptr)
			log_error("Can't find top module in current design!\n");

		if (!design->selected_whole_module(top_module))
			log_cmd_error("Can't handle partially selected module %s!\n", log_id(top_module));

		if (!top_module->processes.empty())
			log_error("Found unmapped processes in module %s: unmapped processes are not supported in AIGER backend!\n", log_id(top_module));
		if (!top_module->memories.empty())
			log_error("Found unmapped memories in module %s: unmapped memories are not supported in AIGER backend!\n", log_id(top_module));

		AigerWriter writer(top_module, zinit_mode, imode, omode, bmode, lmode);
		writer.write_aiger(*f, ascii_mode, miter_mode, symbols_mode);

		if (!map_filename.empty()) {
			rewrite_filename(filename);
			std::ofstream mapf;
			mapf.open(map_filename.c_str(), std::ofstream::trunc);
			if (mapf.fail())
				log_error("Can't open file `%s' for writing: %s\n", map_filename.c_str(), strerror(errno));
			writer.write_map(mapf, verbose_map, no_startoffset);
		}

		if (!yw_map_filename.empty()) {
			std::ofstream mapf;
			mapf.open(yw_map_filename.c_str(), std::ofstream::trunc);

			PrettyJson json;

			if (!json.write_to_file(yw_map_filename))
				log_error("Can't open file `%s' for writing: %s\n", yw_map_filename.c_str(), strerror(errno));
			writer.write_ywmap(json);
		}
	}
} AigerBackend;

PRIVATE_NAMESPACE_END
