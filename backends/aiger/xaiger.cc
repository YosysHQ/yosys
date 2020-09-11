/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Clifford Wolf <clifford@clifford.at>
 *                2019  Eddie Hung <eddie@fpgeh.com>
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

// https://stackoverflow.com/a/46137633
#ifdef _MSC_VER
#include <stdlib.h>
#define bswap32 _byteswap_ulong
#elif defined(__APPLE__)
#include <libkern/OSByteOrder.h>
#define bswap32 OSSwapInt32
#elif defined(__GNUC__)
#define bswap32 __builtin_bswap32
#else
#include <cstdint>
inline static uint32_t bswap32(uint32_t x)
{
	// https://stackoverflow.com/a/27796212
	register uint32_t value = number_to_be_reversed;
	uint8_t lolo = (value >> 0) & 0xFF;
	uint8_t lohi = (value >> 8) & 0xFF;
	uint8_t hilo = (value >> 16) & 0xFF;
	uint8_t hihi = (value >> 24) & 0xFF;
	return (hihi << 24)
		| (hilo << 16)
		| (lohi << 8)
		| (lolo << 0);
}
#endif

#include "kernel/yosys.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/timinginfo.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

inline int32_t to_big_endian(int32_t i32) {
#if __BYTE_ORDER__ == __ORDER_LITTLE_ENDIAN__
	return bswap32(i32);
#elif __BYTE_ORDER__ == __ORDER_BIG_ENDIAN__
	return i32;
#else
#error "Unknown endianness"
#endif
}

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
	Design *design;
	Module *module;
	SigMap sigmap;

	dict<SigBit, State> init_map;
	pool<SigBit> input_bits, output_bits;
	dict<SigBit, SigBit> not_map, alias_map;
	dict<SigBit, pair<SigBit, SigBit>> and_map;
	vector<SigBit> ci_bits, co_bits;
	vector<Cell*> ff_list;
	dict<SigBit, float> arrival_times;

	vector<pair<int, int>> aig_gates;
	vector<int> aig_outputs;
	int aig_m = 0, aig_i = 0, aig_l = 0, aig_o = 0, aig_a = 0;

	dict<SigBit, int> aig_map;
	dict<SigBit, int> ordered_outputs;

	vector<Cell*> box_list;

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
		}

		if (bit == State::Sx || bit == State::Sz) {
			log_debug("Design contains 'x' or 'z' bits. Treating as 1'b0.\n");
			a = aig_map.at(State::S0);
		}

		log_assert(a >= 0);
		aig_map[bit] = a;
		return a;
	}

	XAigerWriter(Module *module, bool dff_mode) : design(module->design), module(module), sigmap(module)
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

		// promote keep wires
		for (auto wire : module->wires())
			if (wire->get_bool_attribute(ID::keep) || wire->get_bool_attribute(ID::abc9_keep))
				sigmap.add(wire);

		for (auto wire : module->wires()) {
			auto it = wire->attributes.find(ID::init);
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

				bool keep = wire->get_bool_attribute(ID::abc9_keep);
				if (wire->port_input || keep)
					input_bits.insert(bit);

				keep = keep || wire->get_bool_attribute(ID::keep);
				if (wire->port_output || keep) {
					if (bit != wirebit)
						alias_map[wirebit] = bit;
					output_bits.insert(wirebit);
				}

				if (it != wire->attributes.end()) {
					auto s = it->second[i];
					if (s != State::Sx) {
						auto r = init_map.insert(std::make_pair(bit, it->second[i]));
						if (!r.second && r.first->second != it->second[i])
							log_error("Bit '%s' has a conflicting (* init *) value.\n", log_signal(bit));
					}
				}
			}
		}

		TimingInfo timing;

		for (auto cell : module->cells()) {
			if (!cell->has_keep_attr()) {
				if (cell->type == ID($_NOT_))
				{
					SigBit A = sigmap(cell->getPort(ID::A).as_bit());
					SigBit Y = sigmap(cell->getPort(ID::Y).as_bit());
					unused_bits.erase(A);
					undriven_bits.erase(Y);
					not_map[Y] = A;
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

				if (dff_mode && cell->type.in(ID($_DFF_N_), ID($_DFF_P_)) && !cell->get_bool_attribute(ID::abc9_keep))
				{
					SigBit D = sigmap(cell->getPort(ID::D).as_bit());
					SigBit Q = sigmap(cell->getPort(ID::Q).as_bit());
					unused_bits.erase(D);
					undriven_bits.erase(Q);
					alias_map[Q] = D;
					ff_list.emplace_back(cell);
					continue;
				}

				if (cell->type.in(ID($specify2), ID($specify3), ID($specrule)))
					continue;
			}

			RTLIL::Module* inst_module = design->module(cell->type);
			if (inst_module && inst_module->get_blackbox_attribute()) {
				bool abc9_flop = false;

				auto it = cell->attributes.find(ID::abc9_box_seq);
				if (it != cell->attributes.end()) {
					log_assert(!cell->has_keep_attr());
					log_assert(cell->parameters.empty());
					int abc9_box_seq = it->second.as_int();
					if (GetSize(box_list) <= abc9_box_seq)
						box_list.resize(abc9_box_seq+1);
					box_list[abc9_box_seq] = cell;
					// Only flop boxes may have arrival times
					//   (all others are combinatorial)
					log_assert(cell->parameters.empty());
					abc9_flop = inst_module->get_bool_attribute(ID::abc9_flop);
					if (!abc9_flop)
						continue;
				}

				if (!timing.count(inst_module->name))
					timing.setup_module(inst_module);
				auto &t = timing.at(inst_module->name).arrival;
				for (const auto &conn : cell->connections()) {
					auto port_wire = inst_module->wire(conn.first);
					if (!port_wire->port_output)
						continue;

					for (int i = 0; i < GetSize(conn.second); i++) {
						auto d = t.at(TimingInfo::NameBit(conn.first,i), 0);
						if (d == 0)
							continue;

#ifndef NDEBUG
						if (ys_debug(1)) {
							static std::set<std::tuple<IdString,IdString,int>> seen;
							if (seen.emplace(inst_module->name, conn.first, i).second) log("%s.%s[%d] abc9_arrival = %d\n",
									log_id(cell->type), log_id(conn.first), i, d);
						}
#endif
						arrival_times[conn.second[i]] = d;
					}
				}

				if (abc9_flop)
					continue;
			}

			bool cell_known = inst_module || cell->known();
			for (const auto &c : cell->connections()) {
				if (c.second.is_fully_const()) continue;
				auto port_wire = inst_module ? inst_module->wire(c.first) : nullptr;
				auto is_input = (port_wire && port_wire->port_input) || !cell_known || cell->input(c.first);
				auto is_output = (port_wire && port_wire->port_output) || !cell_known || cell->output(c.first);
				if (!is_input && !is_output)
					log_error("Connection '%s' on cell '%s' (type '%s') not recognised!\n", log_id(c.first), log_id(cell), log_id(cell->type));

				if (is_input)
					for (auto b : c.second) {
						Wire *w = b.wire;
						if (!w) continue;
						// Do not add as PO if bit is already a PI
						if (input_bits.count(b))
							continue;
						if (!w->port_output || !cell_known) {
							SigBit I = sigmap(b);
							if (I != b)
								alias_map[b] = I;
							output_bits.insert(b);
						}
					}
			}

			//log_warning("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));
		}

		dict<IdString, std::vector<IdString>> box_ports;
		for (auto cell : box_list) {
			log_assert(cell);

			RTLIL::Module* box_module = design->module(cell->type);
			log_assert(box_module);
			log_assert(box_module->has_attribute(ID::abc9_box_id));

			auto r = box_ports.insert(cell->type);
			if (r.second) {
				// Make carry in the last PI, and carry out the last PO
				//   since ABC requires it this way
				IdString carry_in, carry_out;
				for (const auto &port_name : box_module->ports) {
					auto w = box_module->wire(port_name);
					log_assert(w);
					if (w->get_bool_attribute(ID::abc9_carry)) {
						if (w->port_input) {
							if (carry_in != IdString())
								log_error("Module '%s' contains more than one 'abc9_carry' input port.\n", log_id(box_module));
							carry_in = port_name;
						}
						if (w->port_output) {
							if (carry_out != IdString())
								log_error("Module '%s' contains more than one 'abc9_carry' output port.\n", log_id(box_module));
							carry_out = port_name;
						}
					}
					else
						r.first->second.push_back(port_name);
				}

				if (carry_in != IdString() && carry_out == IdString())
					log_error("Module '%s' contains an 'abc9_carry' input port but no output port.\n", log_id(box_module));
				if (carry_in == IdString() && carry_out != IdString())
					log_error("Module '%s' contains an 'abc9_carry' output port but no input port.\n", log_id(box_module));
				if (carry_in != IdString()) {
					r.first->second.push_back(carry_in);
					r.first->second.push_back(carry_out);
				}
			}

			for (auto port_name : r.first->second) {
				auto w = box_module->wire(port_name);
				log_assert(w);
				auto rhs = cell->connections_.at(port_name, SigSpec());
				rhs.append(Const(State::Sx, GetSize(w)-GetSize(rhs)));
				if (w->port_input)
					for (auto b : rhs) {
						SigBit I = sigmap(b);
						if (b == RTLIL::Sx)
							b = State::S0;
						else if (I != b) {
							if (I == RTLIL::Sx)
								alias_map[b] = State::S0;
							else
								alias_map[b] = I;
						}
						co_bits.emplace_back(b);
						unused_bits.erase(I);
					}
				if (w->port_output)
					for (const auto &b : rhs) {
						SigBit O = sigmap(b);
						if (O != b)
							alias_map[O] = b;
						ci_bits.emplace_back(b);
						undriven_bits.erase(O);
					}
			}
		}

		for (auto bit : input_bits)
			undriven_bits.erase(bit);
		for (auto bit : output_bits)
			unused_bits.erase(sigmap(bit));
		for (auto bit : unused_bits)
			undriven_bits.erase(bit);

		// Make all undriven bits a primary input
		for (auto bit : undriven_bits) {
			input_bits.insert(bit);
			undriven_bits.erase(bit);
		}

		struct sort_by_port_id {
			bool operator()(const RTLIL::SigBit& a, const RTLIL::SigBit& b) const {
				return a.wire->port_id < b.wire->port_id ||
				    (a.wire->port_id == b.wire->port_id && a.offset < b.offset);
			}
		};
		input_bits.sort(sort_by_port_id());
		output_bits.sort(sort_by_port_id());

		aig_map[State::S0] = 0;
		aig_map[State::S1] = 1;

		for (const auto &bit : input_bits) {
			aig_m++, aig_i++;
			log_assert(!aig_map.count(bit));
			aig_map[bit] = 2*aig_m;
		}

		for (auto cell : ff_list) {
			const SigBit &q = sigmap(cell->getPort(ID::Q));
			aig_m++, aig_i++;
			log_assert(!aig_map.count(q));
			aig_map[q] = 2*aig_m;
		}

		for (auto &bit : ci_bits) {
			aig_m++, aig_i++;
			// 1'bx may exist here due to a box output
			//   that has been padded to its full width
			if (bit == State::Sx)
				continue;
			log_assert(!aig_map.count(bit));
			aig_map[bit] = 2*aig_m;
		}

		for (auto bit : co_bits) {
			ordered_outputs[bit] = aig_o++;
			aig_outputs.push_back(bit2aig(bit));
		}

		for (const auto &bit : output_bits) {
			ordered_outputs[bit] = aig_o++;
			int aig;
			// Unlike bit2aig() which checks aig_map first for
			//   inout/scc bits, since aig_map will point to
			//   the PI, first attempt to find the NOT/AND driver
			//   before resorting to an aig_map lookup (which
			//   could be another PO)
			if (input_bits.count(bit)) {
				if (not_map.count(bit)) {
					aig = bit2aig(not_map.at(bit)) ^ 1;
				} else if (and_map.count(bit)) {
					auto args = and_map.at(bit);
					int a0 = bit2aig(args.first);
					int a1 = bit2aig(args.second);
					aig = mkgate(a0, a1);
				}
				else
					aig = aig_map.at(bit);
			}
			else
				aig = bit2aig(bit);
			aig_outputs.push_back(aig);
		}

		for (auto cell : ff_list) {
			const SigBit &d = sigmap(cell->getPort(ID::D));
			aig_o++;
			aig_outputs.push_back(aig_map.at(d));
		}
	}

	void write_aiger(std::ostream &f, bool ascii_mode)
	{
		int aig_obc = aig_o;
		int aig_obcj = aig_obc;
		int aig_obcjf = aig_obcj;

		log_assert(aig_m == aig_i + aig_l + aig_a);
		log_assert(aig_obcjf == GetSize(aig_outputs));

		f << stringf("%s %d %d %d %d %d", ascii_mode ? "aag" : "aig", aig_m, aig_i, aig_l, aig_o, aig_a);
		f << stringf("\n");

		if (ascii_mode)
		{
			for (int i = 0; i < aig_i; i++)
				f << stringf("%d\n", 2*i+2);

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

		f << "c";

		auto write_buffer = [](std::stringstream &buffer, int i32) {
			int32_t i32_be = to_big_endian(i32);
			buffer.write(reinterpret_cast<const char*>(&i32_be), sizeof(i32_be));
		};
		std::stringstream h_buffer;
		auto write_h_buffer = std::bind(write_buffer, std::ref(h_buffer), std::placeholders::_1);
		write_h_buffer(1);
		log_debug("ciNum = %d\n", GetSize(input_bits) + GetSize(ff_list) + GetSize(ci_bits));
		write_h_buffer(GetSize(input_bits) + GetSize(ff_list) + GetSize(ci_bits));
		log_debug("coNum = %d\n", GetSize(output_bits) + GetSize(ff_list) + GetSize(co_bits));
		write_h_buffer(GetSize(output_bits) + GetSize(ff_list) + GetSize(co_bits));
		log_debug("piNum = %d\n", GetSize(input_bits) + GetSize(ff_list));
		write_h_buffer(GetSize(input_bits) + GetSize(ff_list));
		log_debug("poNum = %d\n", GetSize(output_bits) + GetSize(ff_list));
		write_h_buffer(GetSize(output_bits) + GetSize(ff_list));
		log_debug("boxNum = %d\n", GetSize(box_list));
		write_h_buffer(GetSize(box_list));

		auto write_buffer_float = [](std::stringstream &buffer, float f32) {
			buffer.write(reinterpret_cast<const char*>(&f32), sizeof(f32));
		};
		std::stringstream i_buffer;
		auto write_i_buffer = std::bind(write_buffer_float, std::ref(i_buffer), std::placeholders::_1);
		for (auto bit : input_bits)
			write_i_buffer(arrival_times.at(bit, 0));
		//std::stringstream o_buffer;
		//auto write_o_buffer = std::bind(write_buffer_float, std::ref(o_buffer), std::placeholders::_1);
		//for (auto bit : output_bits)
		//	write_o_buffer(0);

		if (!box_list.empty() || !ff_list.empty()) {
			dict<IdString, std::tuple<int,int,int>> cell_cache;

			int box_count = 0;
			for (auto cell : box_list) {
				log_assert(cell);
				log_assert(cell->parameters.empty());

				auto r = cell_cache.insert(cell->type);
				auto &v = r.first->second;
				if (r.second) {
					RTLIL::Module* box_module = design->module(cell->type);
					log_assert(box_module);

					int box_inputs = 0, box_outputs = 0;
					for (auto port_name : box_module->ports) {
						RTLIL::Wire *w = box_module->wire(port_name);
						log_assert(w);
						if (w->port_input)
							box_inputs += GetSize(w);
						if (w->port_output)
							box_outputs += GetSize(w);
					}

					std::get<0>(v) = box_inputs;
					std::get<1>(v) = box_outputs;
					std::get<2>(v) = box_module->attributes.at(ID::abc9_box_id).as_int();
				}

				write_h_buffer(std::get<0>(v));
				write_h_buffer(std::get<1>(v));
				write_h_buffer(std::get<2>(v));
				write_h_buffer(box_count++);
			}

			std::stringstream r_buffer;
			auto write_r_buffer = std::bind(write_buffer, std::ref(r_buffer), std::placeholders::_1);
			log_debug("flopNum = %d\n", GetSize(ff_list));
			write_r_buffer(ff_list.size());

			std::stringstream s_buffer;
			auto write_s_buffer = std::bind(write_buffer, std::ref(s_buffer), std::placeholders::_1);
			write_s_buffer(ff_list.size());

			dict<SigSpec, int> clk_to_mergeability;
			for (const auto cell : ff_list) {
				const SigBit &d = sigmap(cell->getPort(ID::D));
				const SigBit &q = sigmap(cell->getPort(ID::Q));

				SigSpec clk_and_pol{sigmap(cell->getPort(ID::C)), cell->type[6] == 'P' ? State::S1 : State::S0};
				auto r = clk_to_mergeability.insert(std::make_pair(clk_and_pol, clk_to_mergeability.size()+1));
				int mergeability = r.first->second;
				log_assert(mergeability > 0);
				write_r_buffer(mergeability);

				State init = init_map.at(q, State::Sx);
				log_debug("Cell '%s' (type %s) has (* init *) value '%s'.\n", log_id(cell), log_id(cell->type), log_signal(init));
				if (init == State::S1)
					write_s_buffer(1);
				else if (init == State::S0)
					write_s_buffer(0);
				else {
					log_assert(init == State::Sx);
					write_s_buffer(2);
				}

				// Use arrival time from output of flop box
				write_i_buffer(arrival_times.at(d, 0));
				//write_o_buffer(0);
			}

			f << "r";
			std::string buffer_str = r_buffer.str();
			int32_t buffer_size_be = to_big_endian(buffer_str.size());
			f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
			f.write(buffer_str.data(), buffer_str.size());

			f << "s";
			buffer_str = s_buffer.str();
			buffer_size_be = to_big_endian(buffer_str.size());
			f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
			f.write(buffer_str.data(), buffer_str.size());

			RTLIL::Design *holes_design;
			auto it = saved_designs.find("$abc9_holes");
			if (it != saved_designs.end())
				holes_design = it->second;
			else
				holes_design = nullptr;
			RTLIL::Module *holes_module = holes_design ? holes_design->module(module->name) : nullptr;
			if (holes_module) {
				std::stringstream a_buffer;
				XAigerWriter writer(holes_module, false /* dff_mode */);
				writer.write_aiger(a_buffer, false /*ascii_mode*/);

				f << "a";
				std::string buffer_str = a_buffer.str();
				int32_t buffer_size_be = to_big_endian(buffer_str.size());
				f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
				f.write(buffer_str.data(), buffer_str.size());
			}
		}

		f << "h";
		std::string buffer_str = h_buffer.str();
		int32_t buffer_size_be = to_big_endian(buffer_str.size());
		f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
		f.write(buffer_str.data(), buffer_str.size());

		f << "i";
		buffer_str = i_buffer.str();
		buffer_size_be = to_big_endian(buffer_str.size());
		f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
		f.write(buffer_str.data(), buffer_str.size());
		//f << "o";
		//buffer_str = o_buffer.str();
		//buffer_size_be = to_big_endian(buffer_str.size());
		//f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
		//f.write(buffer_str.data(), buffer_str.size());

		f << stringf("Generated by %s\n", yosys_version_str);

		design->scratchpad_set_int("write_xaiger.num_ands", and_map.size());
		design->scratchpad_set_int("write_xaiger.num_wires", aig_map.size());
		design->scratchpad_set_int("write_xaiger.num_inputs", input_bits.size());
		design->scratchpad_set_int("write_xaiger.num_outputs", output_bits.size());
	}

	void write_map(std::ostream &f)
	{
		dict<int, string> input_lines;
		dict<int, string> output_lines;

		for (auto wire : module->wires())
		{
			for (int i = 0; i < GetSize(wire); i++)
			{
				RTLIL::SigBit b(wire, i);
				if (input_bits.count(b)) {
					int a = aig_map.at(b);
					log_assert((a & 1) == 0);
					input_lines[a] += stringf("input %d %d %s\n", (a >> 1)-1, wire->start_offset+i, log_id(wire));
				}

				if (output_bits.count(b)) {
					int o = ordered_outputs.at(b);
					output_lines[o] += stringf("output %d %d %s\n", o - GetSize(co_bits), wire->start_offset+i, log_id(wire));
				}
			}
		}

		input_lines.sort();
		for (auto &it : input_lines)
			f << it.second;
		log_assert(input_lines.size() == input_bits.size());

		int box_count = 0;
		for (auto cell : box_list)
			f << stringf("box %d %d %s\n", box_count++, 0, log_id(cell->name));

		output_lines.sort();
		for (auto &it : output_lines)
			f << it.second;
		log_assert(output_lines.size() == output_bits.size());
	}
};

struct XAigerBackend : public Backend {
	XAigerBackend() : Backend("xaiger", "write design to XAIGER file") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    write_xaiger [options] [filename]\n");
		log("\n");
		log("Write the top module (according to the (* top *) attribute or if only one module\n");
		log("is currently selected) to an XAIGER file. Any non $_NOT_, $_AND_, (optionally\n");
		log("$_DFF_N_, $_DFF_P_), or non (* abc9_box *) cells will be converted into psuedo-\n");
		log("inputs and pseudo-outputs. Whitebox contents will be taken from the equivalent\n");
		log("module in the '$abc9_holes' design, if it exists.\n");
		log("\n");
		log("    -ascii\n");
		log("        write ASCII version of AIGER format\n");
		log("\n");
		log("    -map <filename>\n");
		log("        write an extra file with port and box symbols\n");
		log("\n");
		log("    -dff\n");
		log("        write $_DFF_[NP]_ cells\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) override
	{
		bool ascii_mode = false, dff_mode = false;
		std::string map_filename;

		log_header(design, "Executing XAIGER backend.\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-ascii") {
				ascii_mode = true;
				continue;
			}
			if (map_filename.empty() && args[argidx] == "-map" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
			if (args[argidx] == "-dff") {
				dff_mode = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx, !ascii_mode);

		Module *top_module = design->top_module();

		if (top_module == nullptr)
			log_error("Can't find top module in current design!\n");

		if (!design->selected_whole_module(top_module))
			log_cmd_error("Can't handle partially selected module %s!\n", log_id(top_module));

		if (!top_module->processes.empty())
			log_error("Found unmapped processes in module %s: unmapped processes are not supported in XAIGER backend!\n", log_id(top_module));
		if (!top_module->memories.empty())
			log_error("Found unmapped memories in module %s: unmapped memories are not supported in XAIGER backend!\n", log_id(top_module));

		XAigerWriter writer(top_module, dff_mode);
		writer.write_aiger(*f, ascii_mode);

		if (!map_filename.empty()) {
			std::ofstream mapf;
			mapf.open(map_filename.c_str(), std::ofstream::trunc);
			if (mapf.fail())
				log_error("Can't open file `%s' for writing: %s\n", map_filename.c_str(), strerror(errno));
			writer.write_map(mapf);
		}
	}
} XAigerBackend;

PRIVATE_NAMESPACE_END
