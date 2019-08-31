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
	Module *module;
	SigMap sigmap;

	pool<SigBit> input_bits, output_bits;
	dict<SigBit, SigBit> not_map, alias_map;
	dict<SigBit, pair<SigBit, SigBit>> and_map;
	vector<std::tuple<SigBit,RTLIL::Cell*,RTLIL::IdString,int>> ci_bits;
	vector<std::tuple<SigBit,RTLIL::Cell*,RTLIL::IdString,int,int>> co_bits;
	dict<SigBit, float> arrival_times;

	vector<pair<int, int>> aig_gates;
	vector<int> aig_outputs;
	int aig_m = 0, aig_i = 0, aig_l = 0, aig_o = 0, aig_a = 0;

	dict<SigBit, int> aig_map;
	dict<SigBit, int> ordered_outputs;

	vector<Cell*> box_list;
	bool omode = false;

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

	XAigerWriter(Module *module, bool holes_mode=false) : module(module), sigmap(module)
	{
		pool<SigBit> undriven_bits;
		pool<SigBit> unused_bits;
		pool<SigBit> keep_bits;

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
			bool keep = wire->attributes.count("\\keep");

			for (int i = 0; i < GetSize(wire); i++)
			{
				SigBit wirebit(wire, i);
				SigBit bit = sigmap(wirebit);

				if (bit.wire) {
					undriven_bits.insert(bit);
					unused_bits.insert(bit);
				}

				if (keep)
					keep_bits.insert(bit);

				if (wire->port_input || keep) {
					if (bit != wirebit)
						alias_map[bit] = wirebit;
					input_bits.insert(wirebit);
				}

				if (wire->port_output || keep) {
					if (bit != RTLIL::Sx) {
						if (bit != wirebit)
							alias_map[wirebit] = bit;
						output_bits.insert(wirebit);
					}
					else
						log_debug("Skipping PO '%s' driven by 1'bx\n", log_signal(wirebit));
				}
			}
		}

		for (auto bit : input_bits)
			undriven_bits.erase(sigmap(bit));
		for (auto bit : output_bits)
			if (!bit.wire->port_input)
				unused_bits.erase(bit);

		// TODO: Speed up toposort -- ultimately we care about
		//       box ordering, but not individual AIG cells
		dict<SigBit, pool<IdString>> bit_drivers, bit_users;
		TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
		bool abc_box_seen = false;

		for (auto cell : module->selected_cells()) {
			if (cell->type == "$_NOT_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				unused_bits.erase(A);
				undriven_bits.erase(Y);
				not_map[Y] = A;
				if (!holes_mode) {
					toposort.node(cell->name);
					bit_users[A].insert(cell->name);
					bit_drivers[Y].insert(cell->name);
				}
				continue;
			}

			if (cell->type == "$_AND_")
			{
				SigBit A = sigmap(cell->getPort("\\A").as_bit());
				SigBit B = sigmap(cell->getPort("\\B").as_bit());
				SigBit Y = sigmap(cell->getPort("\\Y").as_bit());
				unused_bits.erase(A);
				unused_bits.erase(B);
				undriven_bits.erase(Y);
				and_map[Y] = make_pair(A, B);
				if (!holes_mode) {
					toposort.node(cell->name);
					bit_users[A].insert(cell->name);
					bit_users[B].insert(cell->name);
					bit_drivers[Y].insert(cell->name);
				}
				continue;
			}

			log_assert(!holes_mode);

			RTLIL::Module* inst_module = module->design->module(cell->type);
			if (inst_module && inst_module->attributes.count("\\abc_box_id")) {
				abc_box_seen = true;

				if (!holes_mode) {
					toposort.node(cell->name);
					for (const auto &conn : cell->connections()) {
						auto port_wire = inst_module->wire(conn.first);
						if (port_wire->port_input) {
							// Ignore inout for the sake of topographical ordering
							if (port_wire->port_output) continue;
							for (auto bit : sigmap(conn.second))
								bit_users[bit].insert(cell->name);
						}

						if (port_wire->port_output)
							for (auto bit : sigmap(conn.second))
								bit_drivers[bit].insert(cell->name);
					}
				}
			}
			else {
				bool cell_known = inst_module || cell->known();
				for (const auto &c : cell->connections()) {
					if (c.second.is_fully_const()) continue;
					auto port_wire = inst_module ? inst_module->wire(c.first) : nullptr;
					auto is_input = (port_wire && port_wire->port_input) || !cell_known || cell->input(c.first);
					auto is_output = (port_wire && port_wire->port_output) || !cell_known || cell->output(c.first);
					if (!is_input && !is_output)
						log_error("Connection '%s' on cell '%s' (type '%s') not recognised!\n", log_id(c.first), log_id(cell), log_id(cell->type));

					if (is_input) {
						for (auto b : c.second) {
							Wire *w = b.wire;
							if (!w) continue;
							if (!w->port_output || !cell_known) {
								SigBit I = sigmap(b);
								if (I != b)
									alias_map[b] = I;
								output_bits.insert(b);
								unused_bits.erase(b);

								if (!cell_known)
									keep_bits.insert(b);
							}
						}
					}
					if (is_output) {
						int arrival = 0;
						if (port_wire) {
							auto it = port_wire->attributes.find("\\abc_arrival");
							if (it != port_wire->attributes.end()) {
								if (it->second.flags != 0)
									log_error("Attribute 'abc_arrival' on port '%s' of module '%s' is not an integer.\n", log_id(port_wire), log_id(cell->type));
								arrival = it->second.as_int();
							}
						}

						for (auto b : c.second) {
							Wire *w = b.wire;
							if (!w) continue;
							input_bits.insert(b);
							SigBit O = sigmap(b);
							if (O != b)
								alias_map[O] = b;
							undriven_bits.erase(O);

							if (arrival)
								arrival_times[b] = arrival;
						}
					}
				}
			}

			//log_warning("Unsupported cell type: %s (%s)\n", log_id(cell->type), log_id(cell));
		}

		if (abc_box_seen) {
			for (auto &it : bit_users)
				if (bit_drivers.count(it.first))
					for (auto driver_cell : bit_drivers.at(it.first))
					for (auto user_cell : it.second)
						toposort.edge(driver_cell, user_cell);

#if 0
			toposort.analyze_loops = true;
#endif
			bool no_loops YS_ATTRIBUTE(unused) = toposort.sort();
#if 0
			unsigned i = 0;
			for (auto &it : toposort.loops) {
				log("  loop %d\n", i++);
				for (auto cell_name : it) {
					auto cell = module->cell(cell_name);
					log_assert(cell);
					log("\t%s (%s @ %s)\n", log_id(cell), log_id(cell->type), cell->get_src_attribute().c_str());
				}
			}
#endif
			log_assert(no_loops);

			for (auto cell_name : toposort.sorted) {
				RTLIL::Cell *cell = module->cell(cell_name);
				log_assert(cell);

				RTLIL::Module* box_module = module->design->module(cell->type);
				if (!box_module || !box_module->attributes.count("\\abc_box_id"))
					continue;

				// Fully pad all unused input connections of this box cell with S0
				// Fully pad all undriven output connections of this box cell with anonymous wires
				// NB: Assume box_module->ports are sorted alphabetically
				//     (as RTLIL::Module::fixup_ports() would do)
				for (const auto &port_name : box_module->ports) {
					RTLIL::Wire* w = box_module->wire(port_name);
					log_assert(w);
					auto it = cell->connections_.find(port_name);
					if (w->port_input) {
						RTLIL::SigSpec rhs;
						if (it != cell->connections_.end()) {
							if (GetSize(it->second) < GetSize(w))
								it->second.append(RTLIL::SigSpec(State::S0, GetSize(w)-GetSize(it->second)));
							rhs = it->second;
						}
						else {
							rhs = RTLIL::SigSpec(State::S0, GetSize(w));
							cell->setPort(port_name, rhs);
						}

						int offset = 0;
						for (auto b : rhs.bits()) {
							SigBit I = sigmap(b);
							if (b == RTLIL::Sx)
								b = State::S0;
							else if (I != b) {
								if (I == RTLIL::Sx)
									alias_map[b] = State::S0;
								else
									alias_map[b] = I;
							}
							co_bits.emplace_back(b, cell, port_name, offset++, 0);
							unused_bits.erase(b);
						}
					}
					if (w->port_output) {
						RTLIL::SigSpec rhs;
						auto it = cell->connections_.find(w->name);
						if (it != cell->connections_.end()) {
							if (GetSize(it->second) < GetSize(w))
								it->second.append(module->addWire(NEW_ID, GetSize(w)-GetSize(it->second)));
							rhs = it->second;
						}
						else {
							rhs = module->addWire(NEW_ID, GetSize(w));
							cell->setPort(port_name, rhs);
						}

						int offset = 0;
						for (const auto &b : rhs.bits()) {
							ci_bits.emplace_back(b, cell, port_name, offset++);
							SigBit O = sigmap(b);
							if (O != b)
								alias_map[O] = b;
							undriven_bits.erase(O);

							auto jt = input_bits.find(b);
							if (jt != input_bits.end()) {
								log_assert(keep_bits.count(O));
								input_bits.erase(b);
							}
						}
					}
				}
				box_list.emplace_back(cell);
			}

			// TODO: Free memory from toposort, bit_drivers, bit_users
		}

		for (auto bit : input_bits) {
			if (!output_bits.count(bit))
				continue;
			RTLIL::Wire *wire = bit.wire;
			// If encountering an inout port, or a keep-ed wire, then create a new wire
			// with $inout.out suffix, make it a PO driven by the existing inout, and
			// inherit existing inout's drivers
			if ((wire->port_input && wire->port_output && !undriven_bits.count(bit))
					|| keep_bits.count(bit)) {
				RTLIL::IdString wire_name = wire->name.str() + "$inout.out";
				RTLIL::Wire *new_wire = module->wire(wire_name);
				if (!new_wire)
					new_wire = module->addWire(wire_name, GetSize(wire));
				SigBit new_bit(new_wire, bit.offset);
				module->connect(new_bit, bit);
				if (not_map.count(bit)) {
					auto a = not_map.at(bit);
					not_map[new_bit] = a;
				}
				else if (and_map.count(bit)) {
					auto a = and_map.at(bit);
					and_map[new_bit] = a;
				}
				else if (alias_map.count(bit)) {
					auto a = alias_map.at(bit);
					alias_map[new_bit] = a;
				}
				else
					alias_map[new_bit] = bit;
				output_bits.erase(bit);
				output_bits.insert(new_bit);
			}
		}

		for (auto bit : unused_bits)
			undriven_bits.erase(bit);

		if (!undriven_bits.empty() && !holes_mode) {
			undriven_bits.sort();
			for (auto bit : undriven_bits) {
				log_warning("Treating undriven bit %s.%s like $anyseq.\n", log_id(module), log_signal(bit));
				input_bits.insert(bit);
			}
			log_warning("Treating a total of %d undriven bits in %s like $anyseq.\n", GetSize(undriven_bits), log_id(module));
		}

		if (holes_mode) {
			struct sort_by_port_id {
				bool operator()(const RTLIL::SigBit& a, const RTLIL::SigBit& b) const {
					return a.wire->port_id < b.wire->port_id;
				}
			};
			input_bits.sort(sort_by_port_id());
			output_bits.sort(sort_by_port_id());
		}
		else {
			input_bits.sort();
			output_bits.sort();
		}

		not_map.sort();
		and_map.sort();

		aig_map[State::S0] = 0;
		aig_map[State::S1] = 1;

		for (auto bit : input_bits) {
			aig_m++, aig_i++;
			log_assert(!aig_map.count(bit));
			aig_map[bit] = 2*aig_m;
		}

		for (auto &c : ci_bits) {
			RTLIL::SigBit bit = std::get<0>(c);
			aig_m++, aig_i++;
			aig_map[bit] = 2*aig_m;
		}

		for (auto &c : co_bits) {
			RTLIL::SigBit bit = std::get<0>(c);
			std::get<4>(c) = ordered_outputs[bit] = aig_o++;
			aig_outputs.push_back(bit2aig(bit));
		}

		if (output_bits.empty()) {
			output_bits.insert(State::S0);
			omode = true;
		}

		for (auto bit : output_bits) {
			ordered_outputs[bit] = aig_o++;
			aig_outputs.push_back(bit2aig(bit));
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

		log_assert(!output_bits.empty());
		auto write_buffer = [](std::stringstream &buffer, int i32) {
			int32_t i32_be = to_big_endian(i32);
			buffer.write(reinterpret_cast<const char*>(&i32_be), sizeof(i32_be));
		};
		std::stringstream h_buffer;
		auto write_h_buffer = std::bind(write_buffer, std::ref(h_buffer), std::placeholders::_1);
		write_h_buffer(1);
		log_debug("ciNum = %d\n", GetSize(input_bits) + GetSize(ci_bits));
		write_h_buffer(input_bits.size() + ci_bits.size());
		log_debug("coNum = %d\n", GetSize(output_bits) + GetSize(co_bits));
		write_h_buffer(output_bits.size() + GetSize(co_bits));
		log_debug("piNum = %d\n", GetSize(input_bits));
		write_h_buffer(input_bits.size());
		log_debug("poNum = %d\n", GetSize(output_bits));
		write_h_buffer(output_bits.size());
		log_debug("boxNum = %d\n", GetSize(box_list));
		write_h_buffer(box_list.size());

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

		if (!box_list.empty()) {
			RTLIL::Module *holes_module = module->design->addModule("$__holes__");
			log_assert(holes_module);

			int port_id = 1;
			int box_count = 0;
			for (auto cell : box_list) {
				RTLIL::Module* box_module = module->design->module(cell->type);
				int box_inputs = 0, box_outputs = 0;
				Cell *holes_cell = nullptr;
				if (box_module->get_bool_attribute("\\whitebox")) {
					holes_cell = holes_module->addCell(cell->name, cell->type);
					holes_cell->parameters = cell->parameters;
				}

				// NB: Assume box_module->ports are sorted alphabetically
				//     (as RTLIL::Module::fixup_ports() would do)
				for (const auto &port_name : box_module->ports) {
					RTLIL::Wire *w = box_module->wire(port_name);
					log_assert(w);
					RTLIL::Wire *holes_wire;
					RTLIL::SigSpec port_wire;
					if (w->port_input) {
						for (int i = 0; i < GetSize(w); i++) {
							box_inputs++;
							holes_wire = holes_module->wire(stringf("\\i%d", box_inputs));
							if (!holes_wire) {
								holes_wire = holes_module->addWire(stringf("\\i%d", box_inputs));
								holes_wire->port_input = true;
								holes_wire->port_id = port_id++;
								holes_module->ports.push_back(holes_wire->name);
							}
							if (holes_cell)
								port_wire.append(holes_wire);
						}
						if (!port_wire.empty())
							holes_cell->setPort(w->name, port_wire);
					}
					if (w->port_output) {
						box_outputs += GetSize(w);
						for (int i = 0; i < GetSize(w); i++) {
							if (GetSize(w) == 1)
								holes_wire = holes_module->addWire(stringf("%s.%s", cell->name.c_str(), w->name.c_str()));
							else
								holes_wire = holes_module->addWire(stringf("%s.%s[%d]", cell->name.c_str(), w->name.c_str(), i));
							holes_wire->port_output = true;
							holes_wire->port_id = port_id++;
							holes_module->ports.push_back(holes_wire->name);
							if (holes_cell)
								port_wire.append(holes_wire);
							else
								holes_module->connect(holes_wire, State::S0);
						}
						if (!port_wire.empty())
							holes_cell->setPort(w->name, port_wire);
					}
				}

				write_h_buffer(box_inputs);
				write_h_buffer(box_outputs);
				write_h_buffer(box_module->attributes.at("\\abc_box_id").as_int());
				write_h_buffer(box_count++);
			}

			std::stringstream r_buffer;
			auto write_r_buffer = std::bind(write_buffer, std::ref(r_buffer), std::placeholders::_1);
			write_r_buffer(0);
			f << "r";
			std::string buffer_str = r_buffer.str();
			int32_t buffer_size_be = to_big_endian(buffer_str.size());
			f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
			f.write(buffer_str.data(), buffer_str.size());

			if (holes_module) {
				log_push();

				// NB: fixup_ports() will sort ports by name
				//holes_module->fixup_ports();
				holes_module->check();

				holes_module->design->selection_stack.emplace_back(false);
				RTLIL::Selection& sel = holes_module->design->selection_stack.back();
				sel.select(holes_module);

				// TODO: Should not need to opt_merge if we only instantiate
				//       each box type once...
				Pass::call(holes_module->design, "opt_merge -share_all");

				Pass::call(holes_module->design, "flatten -wb");

				// TODO: Should techmap/aigmap/check all lib_whitebox-es just once,
				//       instead of per write_xaiger call
				Pass::call(holes_module->design, "techmap");
				Pass::call(holes_module->design, "aigmap");
				for (auto cell : holes_module->cells())
					if (!cell->type.in("$_NOT_", "$_AND_"))
						log_error("Whitebox contents cannot be represented as AIG. Please verify whiteboxes are synthesisable.\n");

				holes_module->design->selection_stack.pop_back();

				// Move into a new (temporary) design so that "clean" will only
				// operate (and run checks on) this one module
				RTLIL::Design *holes_design = new RTLIL::Design;
				holes_module->design->modules_.erase(holes_module->name);
				holes_design->add(holes_module);
				Pass::call(holes_design, "clean -purge");

				std::stringstream a_buffer;
				XAigerWriter writer(holes_module, true /* holes_mode */);
				writer.write_aiger(a_buffer, false /*ascii_mode*/);

				delete holes_design;

				f << "a";
				std::string buffer_str = a_buffer.str();
				int32_t buffer_size_be = to_big_endian(buffer_str.size());
				f.write(reinterpret_cast<const char*>(&buffer_size_be), sizeof(buffer_size_be));
				f.write(buffer_str.data(), buffer_str.size());

				log_pop();
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
	}

	void write_map(std::ostream &f, bool verbose_map)
	{
		dict<int, string> input_lines;
		dict<int, string> output_lines;
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
					int a = aig_map.at(b);
					log_assert((a & 1) == 0);
					input_lines[a] += stringf("input %d %d %s\n", (a >> 1)-1, i, log_id(wire));
				}

				if (output_bits.count(b)) {
					int o = ordered_outputs.at(b);
					output_lines[o] += stringf("output %d %d %s\n", o - GetSize(co_bits), i, log_id(wire));
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

		input_lines.sort();
		for (auto &it : input_lines)
			f << it.second;
		log_assert(input_lines.size() == input_bits.size());

		int box_count = 0;
		for (auto cell : box_list)
			f << stringf("box %d %d %s\n", box_count++, 0, log_id(cell->name));

		output_lines.sort();
		if (omode)
			output_lines[State::S0] = "output 0 0 $__dummy__\n";
		for (auto &it : output_lines)
			f << it.second;
		log_assert(output_lines.size() == output_bits.size());

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
		log("        write ASCII version of AIGER format\n");
		log("\n");
		log("    -map <filename>\n");
		log("        write an extra file with port and latch symbols\n");
		log("\n");
		log("    -vmap <filename>\n");
		log("        like -map, but more verbose\n");
		log("\n");
	}
	void execute(std::ostream *&f, std::string filename, std::vector<std::string> args, RTLIL::Design *design) YS_OVERRIDE
	{
		bool ascii_mode = false;
		bool verbose_map = false;
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
			if (map_filename.empty() && args[argidx] == "-vmap" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				verbose_map = true;
				continue;
			}
			break;
		}
		extra_args(f, filename, args, argidx);

		Module *top_module = design->top_module();

		if (top_module == nullptr)
			log_error("Can't find top module in current design!\n");

		XAigerWriter writer(top_module);
		writer.write_aiger(*f, ascii_mode);

		if (!map_filename.empty()) {
			std::ofstream mapf;
			mapf.open(map_filename.c_str(), std::ofstream::trunc);
			if (mapf.fail())
				log_error("Can't open file `%s' for writing: %s\n", map_filename.c_str(), strerror(errno));
			writer.write_map(mapf, verbose_map);
		}
	}
} XAigerBackend;

PRIVATE_NAMESPACE_END
