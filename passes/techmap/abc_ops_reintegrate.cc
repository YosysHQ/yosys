/*
 *  yosys -- Yosys Open SYnthesis Suite
 *
 *  Copyright (C) 2012  Claire Xenia Wolf <claire@yosyshq.com>
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

#include "kernel/register.h"
#include "kernel/sigtools.h"
#include "kernel/utils.h"
#include "kernel/newcelltypes.h"
#include "kernel/timinginfo.h"

USING_YOSYS_NAMESPACE
PRIVATE_NAMESPACE_BEGIN

int map_autoidx;

inline std::string remap_name(RTLIL::IdString abc9_name)
{
	return stringf("$abc$%d$%s", map_autoidx, abc9_name.c_str()+1);
}

void reintegrate(RTLIL::Module *module, bool dff_mode, std::string map_filename)
{
	auto design = module->design;
	log_assert(design);

	map_autoidx = autoidx++;

	RTLIL::Module *mapped_mod = design->module(stringf("%s$abc9", module->name));
	if (mapped_mod == NULL)
		log_error("ABC output file does not contain a module `%s$abc'.\n", module);

	int input_count = design->scratchpad_get_int("read_aiger.inputs", 0);
	int output_count = design->scratchpad_get_int("read_aiger.outputs", 0);
	int co_count = design->scratchpad_get_int("read_aiger.co_count", 0);

	dict<RTLIL::IdString, std::pair<int,int>> wideports_cache;

	if (!map_filename.empty()) {
		std::ifstream mf(map_filename);
		std::string type, symbol;
		int variable, index;
		while (mf >> type >> variable >> index >> symbol) {
			RTLIL::IdString escaped_s = RTLIL::escape_id(symbol);
			if (type == "input") {
				log_assert(variable < input_count);
				RTLIL::Wire* wire = mapped_mod->wire(stringf("$aiger$i%d", variable + 1));
				log_assert(wire);
				log_assert(wire->port_input);
				log_debug("Renaming input %s", wire);

				RTLIL::Wire *existing = nullptr;
				if (index == 0) {
					// Cope with the fact that a CI might be identical
					// to a PI (necessary due to ABC); in those cases
					// simply connect the latter to the former
					existing = mapped_mod->wire(escaped_s);
					if (!existing)
						mapped_mod->rename(wire, escaped_s);
					else {
						wire->port_input = false;
						mapped_mod->connect(wire, existing);
					}
					log_debug(" -> %s\n", escaped_s);
				}
				else {
					RTLIL::IdString indexed_name = stringf("%s[%d]", escaped_s, index);
					existing = mapped_mod->wire(indexed_name);
					if (!existing)
						mapped_mod->rename(wire, indexed_name);
					else {
						mapped_mod->connect(wire, existing);
						wire->port_input = false;
					}
					log_debug(" -> %s\n", indexed_name);
				}

				if (!existing) {
					auto r = wideports_cache.insert(escaped_s);
					if (r.second) {
						r.first->second.first = index;
						r.first->second.second = index;
					}
					else {
						r.first->second.first = std::min(r.first->second.first, index);
						r.first->second.second = std::max(r.first->second.second, index);
					}
				}
			}
			else if (type == "output") {
				log_assert(variable + co_count < output_count);
				RTLIL::Wire* wire = mapped_mod->wire(stringf("$aiger$o%d", variable + co_count));
				log_assert(wire);
				log_assert(wire->port_output);
				log_debug("Renaming output %s", wire);

				RTLIL::Wire *existing;
				if (index == 0) {
					// Cope with the fact that a CO might be identical
					// to a PO (necessary due to ABC); in those cases
					// simply connect the latter to the former
					existing = mapped_mod->wire(escaped_s);
					if (!existing)
						mapped_mod->rename(wire, escaped_s);
					else {
						wire->port_output = false;
						existing->port_output = true;
						mapped_mod->connect(wire, existing);
						wire = existing;
					}
					log_debug(" -> %s\n", escaped_s);
				}
				else {
					RTLIL::IdString indexed_name = stringf("%s[%d]", escaped_s, index);
					existing = mapped_mod->wire(indexed_name);
					if (!existing)
						mapped_mod->rename(wire, indexed_name);
					else {
						wire->port_output = false;
						existing->port_output = true;
						mapped_mod->connect(wire, existing);
					}
					log_debug(" -> %s\n", indexed_name);
				}

				if (!existing) {
					auto r = wideports_cache.insert(escaped_s);
					if (r.second) {
						r.first->second.first = index;
						r.first->second.second = index;
					}
					else {
						r.first->second.first = std::min(r.first->second.first, index);
						r.first->second.second = std::max(r.first->second.second, index);
					}
				}
			}
			else if (type == "box") {
				RTLIL::Cell* cell = mapped_mod->cell(stringf("$box%d", variable));
				if (!cell)
					log_debug("Box %d (%s) no longer exists.\n", variable, escaped_s.unescape());
				else
					mapped_mod->rename(cell, escaped_s);
			}
			else
				log_error("Symbol type '%s' not recognised.\n", type);
		}
	}

	for (auto &wp : wideports_cache) {
		auto name = wp.first;
		int min = wp.second.first;
		int max = wp.second.second;
		if (min == 0 && max == 0)
			continue;

		RTLIL::Wire *wire = mapped_mod->wire(name);
		if (wire)
			mapped_mod->rename(wire, RTLIL::escape_id(stringf("%s[%d]", name, 0)));

		// Do not make ports with a mix of input/output into
		// wide ports
		bool port_input = false, port_output = false;
		for (int i = min; i <= max; i++) {
			RTLIL::IdString other_name = name.str() + stringf("[%d]", i);
			RTLIL::Wire *other_wire = mapped_mod->wire(other_name);
			if (other_wire) {
				port_input = port_input || other_wire->port_input;
				port_output = port_output || other_wire->port_output;
			}
		}

		wire = mapped_mod->addWire(name, max-min+1);
		wire->start_offset = min;
		wire->port_input = port_input;
		wire->port_output = port_output;

		for (int i = min; i <= max; i++) {
			RTLIL::IdString other_name = stringf("%s[%d]", name, i);
			RTLIL::Wire *other_wire = mapped_mod->wire(other_name);
			if (other_wire) {
				other_wire->port_input = false;
				other_wire->port_output = false;
				if (wire->port_input)
					mapped_mod->connect(other_wire, SigSpec(wire, i-min));
				else
					mapped_mod->connect(SigSpec(wire, i-min), other_wire);
			}
		}
	}

	mapped_mod->fixup_ports();

	for (auto w : mapped_mod->wires()) {
		auto nw = module->addWire(remap_name(w->name), GetSize(w));
		nw->start_offset = w->start_offset;
		// Remove all (* init *) since they only exist on $_DFF_[NP]_
		w->attributes.erase(ID::init);
	}

	dict<IdString,std::vector<IdString>> box_ports;

	for (auto m : design->modules()) {
		if (!m->attributes.count(ID::abc9_box_id))
			continue;

		auto r = box_ports.insert(m->name);
		if (!r.second)
			continue;

		// Make carry in the last PI, and carry out the last PO
		//   since ABC requires it this way
		IdString carry_in, carry_out;
		for (const auto &port_name : m->ports) {
			auto w = m->wire(port_name);
			log_assert(w);
			if (w->get_bool_attribute(ID::abc9_carry)) {
				log_assert(w->port_input != w->port_output);
				if (w->port_input)
					carry_in = port_name;
				else if (w->port_output)
					carry_out = port_name;
			}
			else
				r.first->second.push_back(port_name);
		}

		if (carry_in != IdString()) {
			r.first->second.push_back(carry_in);
			r.first->second.push_back(carry_out);
		}
	}

	SigMap initmap;
	if (dff_mode) {
		// Build a sigmap prioritising bits with (* init *)
		initmap.set(module);
		for (auto w : module->wires()) {
			auto it = w->attributes.find(ID::init);
			if (it == w->attributes.end())
				continue;
			for (auto i = 0; i < GetSize(w); i++)
				if (it->second[i] == State::S0 || it->second[i] == State::S1)
					initmap.add(w);
		}
	}

	std::vector<Cell*> boxes;
	for (auto cell : module->cells().to_vector()) {
		if (cell->has_keep_attr())
			continue;

		// Short out (so that existing name can be preserved) and remove
		//   $_DFF_[NP]_ cells since flop box already has all the information
		//   we need to reconstruct them
		if (dff_mode && cell->type.in(ID($_DFF_N_), ID($_DFF_P_)) && !cell->get_bool_attribute(ID::abc9_keep)) {
			SigBit Q = cell->getPort(ID::Q);
			module->connect(Q, cell->getPort(ID::D));
			module->remove(cell);
			auto Qi = initmap(Q);
			auto it = Qi.wire->attributes.find(ID::init);
			if (it != Qi.wire->attributes.end())
				it->second.set(Qi.offset, State::Sx);
		}
		else if (cell->type.in(ID($_AND_), ID($_NOT_)))
			module->remove(cell);
		else if (cell->attributes.erase(ID::abc9_box_seq))
			boxes.emplace_back(cell);
	}

	dict<SigBit, pool<IdString>> bit_drivers, bit_users;
	TopoSort<IdString, RTLIL::sort_by_id_str> toposort;
	dict<RTLIL::Cell*,RTLIL::Cell*> not2drivers;
	dict<SigBit, std::vector<RTLIL::Cell*>> bit2sinks;

	std::map<IdString, int> cell_stats;
	for (auto mapped_cell : mapped_mod->cells())
	{
		// Short out $_FF_ cells since the flop box already has
		//   all the information we need to reconstruct cell
		if (dff_mode && mapped_cell->type == ID($_FF_)) {
			SigBit D = mapped_cell->getPort(ID::D);
			SigBit Q = mapped_cell->getPort(ID::Q);
			if (D.wire)
				D.wire = module->wires_.at(remap_name(D.wire->name));
			Q.wire = module->wires_.at(remap_name(Q.wire->name));
			module->connect(Q, D);
			continue;
		}

		// TODO: Speed up toposort -- we care about NOT ordering only
		toposort.node(mapped_cell->name);

		if (mapped_cell->type == ID($_NOT_)) {
			RTLIL::SigBit a_bit = mapped_cell->getPort(ID::A);
			RTLIL::SigBit y_bit = mapped_cell->getPort(ID::Y);
			bit_users[a_bit].insert(mapped_cell->name);
			// Ignore inouts for topo ordering
			if (y_bit.wire && !(y_bit.wire->port_input && y_bit.wire->port_output))
				bit_drivers[y_bit].insert(mapped_cell->name);

			if (!a_bit.wire) {
				mapped_cell->setPort(ID::Y, module->addWire(NEW_ID));
				RTLIL::Wire *wire = module->wire(remap_name(y_bit.wire->name));
				log_assert(wire);
				module->connect(RTLIL::SigBit(wire, y_bit.offset), State::S1);
			}
			else {
				RTLIL::Cell* driver_lut = nullptr;
				// ABC can return NOT gates that drive POs
				if (!a_bit.wire->port_input) {
					// If it's not a NOT gate that that comes from a PI directly,
					// find the driver LUT and clone that to guarantee that we won't
					// increase the max logic depth
					// (TODO: Optimise by not cloning unless will increase depth)
					RTLIL::IdString driver_name;
					if (GetSize(a_bit.wire) == 1)
						driver_name = stringf("$lut%s", a_bit.wire->name);
					else
						driver_name = stringf("$lut%s[%d]", a_bit.wire->name, a_bit.offset);
					driver_lut = mapped_mod->cell(driver_name);
				}

				if (!driver_lut) {
					// If a driver couldn't be found (could be from PI or box CI)
					// then implement using a LUT
					RTLIL::Cell *cell = module->addLut(remap_name(stringf("$lut%s", mapped_cell->name)),
							RTLIL::SigBit(module->wires_.at(remap_name(a_bit.wire->name)), a_bit.offset),
							RTLIL::SigBit(module->wires_.at(remap_name(y_bit.wire->name)), y_bit.offset),
							RTLIL::Const::from_string("01"));
					bit2sinks[cell->getPort(ID::A)].push_back(cell);
					cell_stats[ID($lut)]++;
				}
				else
					not2drivers[mapped_cell] = driver_lut;
			}
			continue;
		}

		if (mapped_cell->type == ID($lut)) {
			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = mapped_cell->parameters;
			cell->attributes = mapped_cell->attributes;

			for (auto &mapped_conn : mapped_cell->connections()) {
				RTLIL::SigSpec newsig;
				for (auto c : mapped_conn.second.chunks()) {
					if (c.width == 0)
						continue;
					//log_assert(c.width == 1);
					if (c.wire)
						c.wire = module->wires_.at(remap_name(c.wire->name));
					newsig.append(c);
				}
				cell->setPort(mapped_conn.first, newsig);

				if (cell->input(mapped_conn.first)) {
					for (auto i : newsig)
						bit2sinks[i].push_back(cell);
					for (auto i : mapped_conn.second)
						bit_users[i].insert(mapped_cell->name);
				}
				if (cell->output(mapped_conn.first))
					for (auto i : mapped_conn.second)
						// Ignore inouts for topo ordering
						if (i.wire && !(i.wire->port_input && i.wire->port_output))
							bit_drivers[i].insert(mapped_cell->name);
			}
		}
		else {
			RTLIL::Cell *existing_cell = module->cell(mapped_cell->name);
			if (!existing_cell)
				log_error("Cannot find existing box cell with name '%s' in original design.\n", mapped_cell);

			if (existing_cell->type.begins_with("$paramod$__ABC9_DELAY\\DELAY=")) {
				SigBit I = mapped_cell->getPort(ID(i));
				SigBit O = mapped_cell->getPort(ID(o));
				if (I.wire)
					I.wire = module->wires_.at(remap_name(I.wire->name));
				log_assert(O.wire);
				O.wire = module->wires_.at(remap_name(O.wire->name));
				module->connect(O, I);
				continue;
			}

			RTLIL::Module* box_module = design->module(existing_cell->type);
			log_assert(existing_cell->parameters.empty());
			log_assert(mapped_cell->type == stringf("$__boxid%d", box_module->attributes.at(ID::abc9_box_id).as_int()));
			mapped_cell->type = existing_cell->type;

			RTLIL::Cell *cell = module->addCell(remap_name(mapped_cell->name), mapped_cell->type);
			cell->parameters = existing_cell->parameters;
			cell->attributes = existing_cell->attributes;
			module->swap_names(cell, existing_cell);

			auto jt = mapped_cell->connections_.find(ID(i));
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec inputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);
			jt = mapped_cell->connections_.find(ID(o));
			log_assert(jt != mapped_cell->connections_.end());
			SigSpec outputs = std::move(jt->second);
			mapped_cell->connections_.erase(jt);

			auto abc9_flop = box_module->get_bool_attribute(ID::abc9_flop);
			if (abc9_flop) {
				// Link this sole flop box output to the output of the existing
				//   flop box, so that any (public) signal it drives will be
				//   preserved
				SigBit old_q;
				for (const auto &port_name : box_ports.at(existing_cell->type)) {
					RTLIL::Wire *w = box_module->wire(port_name);
					log_assert(w);
					if (!w->port_output)
						continue;
					log_assert(old_q == SigBit());
					log_assert(GetSize(w) == 1);
					old_q = existing_cell->getPort(port_name);
				}
				auto new_q = outputs[0];
				new_q.wire = module->wires_.at(remap_name(new_q.wire->name));
				module->connect(old_q,  new_q);
			}
			else {
				for (const auto &i : inputs)
					bit_users[i].insert(mapped_cell->name);
				for (const auto &i : outputs)
					// Ignore inouts for topo ordering
					if (i.wire && !(i.wire->port_input && i.wire->port_output))
						bit_drivers[i].insert(mapped_cell->name);
			}

			int input_count = 0, output_count = 0;
			for (const auto &port_name : box_ports.at(existing_cell->type)) {
				RTLIL::Wire *w = box_module->wire(port_name);
				log_assert(w);

				SigSpec sig;
				if (w->port_input) {
					sig = inputs.extract(input_count, GetSize(w));
					input_count += GetSize(w);
				}
				if (w->port_output) {
					sig = outputs.extract(output_count, GetSize(w));
					output_count += GetSize(w);
				}

				SigSpec newsig;
				for (auto c : sig.chunks()) {
					if (c.width == 0)
						continue;
					//log_assert(c.width == 1);
					if (c.wire)
						c.wire = module->wires_.at(remap_name(c.wire->name));
					newsig.append(c);
				}

				if (w->port_input && !abc9_flop)
					for (const auto &i : newsig)
						bit2sinks[i].push_back(cell);

				cell->setPort(port_name, std::move(newsig));
			}
		}

		cell_stats[mapped_cell->type]++;
	}

	for (auto cell : boxes)
		module->remove(cell);

	// Copy connections (and rename) from mapped_mod to module
	for (auto conn : mapped_mod->connections()) {
		if (!conn.first.is_fully_const()) {
			std::vector<RTLIL::SigChunk> chunks = conn.first.chunks();
			for (auto &c : chunks)
				c.wire = module->wires_.at(remap_name(c.wire->name));
			conn.first = std::move(chunks);
		}
		if (!conn.second.is_fully_const()) {
			std::vector<RTLIL::SigChunk> chunks = conn.second.chunks();
			for (auto &c : chunks)
				if (c.wire)
					c.wire = module->wires_.at(remap_name(c.wire->name));
			conn.second = std::move(chunks);
		}
		module->connect(conn);
	}

	for (auto &it : cell_stats)
		log("ABC RESULTS:   %15s cells: %8d\n", it.first, it.second);
	int in_wires = 0, out_wires = 0;

	// Stitch in mapped_mod's inputs/outputs into module
	for (auto port : mapped_mod->ports) {
		RTLIL::Wire *mapped_wire = mapped_mod->wire(port);
		RTLIL::Wire *wire = module->wire(port);
		log_assert(wire);

		RTLIL::Wire *remap_wire = module->wire(remap_name(port));
		RTLIL::SigSpec signal(wire, remap_wire->start_offset-wire->start_offset, GetSize(remap_wire));
		log_assert(GetSize(signal) >= GetSize(remap_wire));

		RTLIL::SigSig conn;
		if (mapped_wire->port_output) {
			conn.first = signal;
			conn.second = remap_wire;
			out_wires++;
			module->connect(conn);
		}
		else if (mapped_wire->port_input) {
			conn.first = remap_wire;
			conn.second = signal;
			in_wires++;
			module->connect(conn);
		}
	}

	// ABC9 will return $_NOT_ gates in its mapping (since they are
	//   treated as being "free"), in particular driving primary
	//   outputs (real primary outputs, or cells treated as blackboxes)
	//   or driving box inputs.
	// Instead of just mapping those $_NOT_ gates into 1-input $lut-s
	//   at an area and delay cost, see if it is possible to push
	//   this $_NOT_ into the driving LUT, or into all sink LUTs.
	// When this is not possible, (i.e. this signal drives two primary
	//   outputs, only one of which is complemented) and when the driver
	//   is a LUT, then clone the LUT so that it can be inverted without
	//   increasing depth/delay.
	for (auto &it : bit_users)
		if (bit_drivers.count(it.first))
			for (auto driver_cell : bit_drivers.at(it.first))
			for (auto user_cell : it.second)
				toposort.edge(driver_cell, user_cell);
	bool no_loops = toposort.sort();
	log_assert(no_loops);

	for (auto ii = toposort.sorted.rbegin(); ii != toposort.sorted.rend(); ii++) {
		RTLIL::Cell *not_cell = mapped_mod->cell(*ii);
		log_assert(not_cell);
		if (not_cell->type != ID($_NOT_))
			continue;
		auto it = not2drivers.find(not_cell);
		if (it == not2drivers.end())
			continue;
		RTLIL::Cell *driver_lut = it->second;
		RTLIL::SigBit a_bit = not_cell->getPort(ID::A);
		RTLIL::SigBit y_bit = not_cell->getPort(ID::Y);
		RTLIL::Const driver_mask;

		a_bit.wire = module->wires_.at(remap_name(a_bit.wire->name));
		y_bit.wire = module->wires_.at(remap_name(y_bit.wire->name));

		auto jt = bit2sinks.find(a_bit);
		if (jt == bit2sinks.end())
			goto clone_lut;

		for (auto sink_cell : jt->second)
			if (sink_cell->type != ID($lut))
				goto clone_lut;

		// Push downstream LUTs past inverter
		for (auto sink_cell : jt->second) {
			SigSpec A = sink_cell->getPort(ID::A);
			RTLIL::Const mask = sink_cell->getParam(ID::LUT);
			int index = 0;
			for (; index < GetSize(A); index++)
				if (A[index] == a_bit)
					break;
			log_assert(index < GetSize(A));
			int i = 0;
			while (i < GetSize(mask)) {
				for (int j = 0; j < (1 << index); j++) {
					State bit = mask[i+j];
					mask.set(i+j, mask[i+j+(1 << index)]);
					mask.set(i+j+(1 << index), bit);
				}
				i += 1 << (index+1);
			}
			A[index] = y_bit;
			sink_cell->setPort(ID::A, A);
			sink_cell->setParam(ID::LUT, mask);
		}

		// Since we have rewritten all sinks (which we know
		// to be only LUTs) to be after the inverter, we can
		// go ahead and clone the LUT with the expectation
		// that the original driving LUT will become dangling
		// and get cleaned away
clone_lut:
		driver_mask = driver_lut->getParam(ID::LUT);
		for (auto b : driver_mask) {
			if (b == RTLIL::State::S0) b = RTLIL::State::S1;
			else if (b == RTLIL::State::S1) b = RTLIL::State::S0;
		}
		auto cell = module->addLut(NEW_ID,
				driver_lut->getPort(ID::A),
				y_bit,
				driver_mask);
		for (auto &bit : cell->connections_.at(ID::A)) {
			bit.wire = module->wires_.at(remap_name(bit.wire->name));
			bit2sinks[bit].push_back(cell);
		}
	}

	log("ABC RESULTS:           input signals: %8d\n", in_wires);
	log("ABC RESULTS:          output signals: %8d\n", out_wires);

	design->remove(mapped_mod);
}

struct AbcOpsReintegratePass : public Pass {
	AbcOpsReintegratePass() : Pass("abc_ops_reintegrate", "reintegrate ABC mapped design into module") { }
	void help() override
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    abc_ops_reintegrate [options] [selection]\n");
		log("\n");
		log("For each selected module, re-integrate the module '<module-name>$abc9'\n");
		log("by first recovering ABC9 boxes, and then stitching in the remaining\n");
		log("primary inputs and outputs.\n");
		log("\n");
		log("    -dff\n");
		log("        consider flop cells (those instantiating modules marked with\n");
		log("        (* abc9_flop *)) during -prep_{delays,xaiger,box}.\n");
		log("\n");
		log("    -map <filename>\n");
		log("        read file with port and latch symbols\n");
		log("\n");
	}
	void execute(std::vector<std::string> args, RTLIL::Design *design) override
	{
		log_header(design, "Executing ABC_OPS_REINTEGRATE pass (reintegrate ABC mapped design into module).\n");

		bool dff_mode = false;
		std::string map_filename;

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++) {
			std::string arg = args[argidx];
			if (arg == "-dff") {
				dff_mode = true;
				continue;
			}
			if (map_filename.empty() && arg == "-map" && argidx+1 < args.size()) {
				map_filename = args[++argidx];
				continue;
			}
		}
		extra_args(args, argidx, design);

		for (auto mod : design->selected_modules()) {
			if (mod->processes.size() > 0) {
				log("Skipping module %s as it contains processes.\n", mod);
				continue;
			}

			if (!design->selected_whole_module(mod))
				log_error("Can't handle partially selected module %s!\n", mod);

			reintegrate(mod, dff_mode, map_filename);
		}
	}
} AbcOpsReintegratePass;

PRIVATE_NAMESPACE_END
