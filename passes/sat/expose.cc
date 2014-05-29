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

#include "kernel/register.h"
#include "kernel/celltypes.h"
#include "kernel/sigtools.h"
#include "kernel/rtlil.h"
#include "kernel/log.h"

struct dff_map_info_t {
	RTLIL::SigSpec sig_d, sig_clk, sig_arst;
	bool clk_polarity, arst_polarity;
	RTLIL::Const arst_value;
	std::vector<std::string> cells;
};

struct dff_map_bit_info_t {
	RTLIL::SigBit bit_d, bit_clk, bit_arst;
	bool clk_polarity, arst_polarity;
	RTLIL::State arst_value;
	RTLIL::Cell *cell;
};

static bool consider_wire(RTLIL::Wire *wire, std::map<std::string, dff_map_info_t> &dff_dq_map)
{
	if (wire->name[0] == '$' || dff_dq_map.count(wire->name))
		return false;
	if (wire->port_input)
		return false;
	return true;
}

static bool consider_cell(RTLIL::Design *design, std::set<std::string> &dff_cells, RTLIL::Cell *cell)
{
	if (cell->name[0] == '$' || dff_cells.count(cell->name))
		return false;
	if (cell->type.at(0) == '\\' && !design->modules.count(cell->type))
		return false;
	return true;
}

static bool compare_wires(RTLIL::Wire *wire1, RTLIL::Wire *wire2)
{
	log_assert(wire1->name == wire2->name);
	if (wire1->width != wire2->width)
		return false;
	return true;
}

static bool compare_cells(RTLIL::Cell *cell1, RTLIL::Cell *cell2)
{
	log_assert(cell1->name == cell2->name);
	if (cell1->type != cell2->type)
		return false;
	if (cell1->parameters != cell2->parameters)
		return false;
	return true;
}

static void find_dff_wires(std::set<std::string> &dff_wires, RTLIL::Module *module)
{
	CellTypes ct;
	ct.setup_internals_mem();
	ct.setup_stdcells_mem();

	SigMap sigmap(module);
	SigPool dffsignals;

	for (auto &it : module->cells) {
		if (ct.cell_known(it.second->type) && it.second->connections.count("\\Q"))
			dffsignals.add(sigmap(it.second->connections.at("\\Q")));
	}

	for (auto &it : module->wires) {
		if (dffsignals.check_any(it.second))
			dff_wires.insert(it.first);
	}
}

static void create_dff_dq_map(std::map<std::string, dff_map_info_t> &map, RTLIL::Design *design, RTLIL::Module *module)
{
	std::map<RTLIL::SigBit, dff_map_bit_info_t> bit_info;
	SigMap sigmap(module);

	for (auto &it : module->cells)
	{
		if (!design->selected(module, it.second))
			continue;

		dff_map_bit_info_t info;
		info.bit_d = RTLIL::State::Sm;
		info.bit_clk = RTLIL::State::Sm;
		info.bit_arst = RTLIL::State::Sm;
		info.clk_polarity = false;
		info.arst_polarity = false;
		info.arst_value = RTLIL::State::Sm;
		info.cell = it.second;

		if (info.cell->type == "$dff") {
			info.bit_clk = sigmap(info.cell->connections.at("\\CLK")).to_single_sigbit();
			info.clk_polarity = info.cell->parameters.at("\\CLK_POLARITY").as_bool();
			std::vector<RTLIL::SigBit> sig_d = sigmap(info.cell->connections.at("\\D")).to_sigbit_vector();
			std::vector<RTLIL::SigBit> sig_q = sigmap(info.cell->connections.at("\\Q")).to_sigbit_vector();
			for (size_t i = 0; i < sig_d.size(); i++) {
				info.bit_d = sig_d.at(i);
				bit_info[sig_q.at(i)] = info;
			}
			continue;
		}

		if (info.cell->type == "$adff") {
			info.bit_clk = sigmap(info.cell->connections.at("\\CLK")).to_single_sigbit();
			info.bit_arst = sigmap(info.cell->connections.at("\\ARST")).to_single_sigbit();
			info.clk_polarity = info.cell->parameters.at("\\CLK_POLARITY").as_bool();
			info.arst_polarity = info.cell->parameters.at("\\ARST_POLARITY").as_bool();
			std::vector<RTLIL::SigBit> sig_d = sigmap(info.cell->connections.at("\\D")).to_sigbit_vector();
			std::vector<RTLIL::SigBit> sig_q = sigmap(info.cell->connections.at("\\Q")).to_sigbit_vector();
			std::vector<RTLIL::State> arst_value = info.cell->parameters.at("\\ARST_VALUE").bits;
			for (size_t i = 0; i < sig_d.size(); i++) {
				info.bit_d = sig_d.at(i);
				info.arst_value = arst_value.at(i);
				bit_info[sig_q.at(i)] = info;
			}
			continue;
		}

		if (info.cell->type == "$_DFF_N_" || info.cell->type == "$_DFF_P_") {
			info.bit_clk = sigmap(info.cell->connections.at("\\C")).to_single_sigbit();
			info.clk_polarity = info.cell->type == "$_DFF_P_";
			info.bit_d = sigmap(info.cell->connections.at("\\D")).to_single_sigbit();
			bit_info[sigmap(info.cell->connections.at("\\Q")).to_single_sigbit()] = info;
			continue;
		}

		if (info.cell->type.size() == 10 && info.cell->type.substr(0, 6) == "$_DFF_") {
			info.bit_clk = sigmap(info.cell->connections.at("\\C")).to_single_sigbit();
			info.bit_arst = sigmap(info.cell->connections.at("\\R")).to_single_sigbit();
			info.clk_polarity = info.cell->type[6] == 'P';
			info.arst_polarity = info.cell->type[7] == 'P';
			info.arst_value = info.cell->type[0] == '1' ? RTLIL::State::S1 : RTLIL::State::S0;
			info.bit_d = sigmap(info.cell->connections.at("\\D")).to_single_sigbit();
			bit_info[sigmap(info.cell->connections.at("\\Q")).to_single_sigbit()] = info;
			continue;
		}
	}

	std::map<std::string, dff_map_info_t> empty_dq_map;
	for (auto &it : module->wires)
	{
		if (!consider_wire(it.second, empty_dq_map))
			continue;

		std::vector<RTLIL::SigBit> bits_q = sigmap(it.second).to_sigbit_vector();
		std::vector<RTLIL::SigBit> bits_d;
		std::vector<RTLIL::State> arst_value;
		std::set<RTLIL::Cell*> cells;

		if (bits_q.empty() || !bit_info.count(bits_q.front()))
			continue;

		dff_map_bit_info_t ref_info = bit_info.at(bits_q.front());
		for (auto &bit : bits_q) {
			if (!bit_info.count(bit))
				break;
			dff_map_bit_info_t info = bit_info.at(bit);
			if (info.bit_clk != ref_info.bit_clk)
				break;
			if (info.bit_arst != ref_info.bit_arst)
				break;
			if (info.clk_polarity != ref_info.clk_polarity)
				break;
			if (info.arst_polarity != ref_info.arst_polarity)
				break;
			bits_d.push_back(info.bit_d);
			arst_value.push_back(info.arst_value);
			cells.insert(info.cell);
		}

		if (bits_d.size() != bits_q.size())
			continue;

		dff_map_info_t info;
		info.sig_d = bits_d;
		info.sig_clk = ref_info.bit_clk;
		info.sig_arst = ref_info.bit_arst;
		info.clk_polarity = ref_info.clk_polarity;
		info.arst_polarity = ref_info.arst_polarity;
		info.arst_value = arst_value;
		for (auto it : cells)
			info.cells.push_back(it->name);
		map[it.first] = info;
	}
}

static void add_new_wire(RTLIL::Module *module, RTLIL::Wire *wire)
{
	if (module->count_id(wire->name))
		log_error("Attempting to create wire %s, but a wire of this name exists already! Hint: Try another value for -sep.\n", RTLIL::id2cstr(wire->name));
	module->add(wire);
}

struct ExposePass : public Pass {
	ExposePass() : Pass("expose", "convert internal signals to module ports") { }
	virtual void help()
	{
		//   |---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|---v---|
		log("\n");
		log("    expose [options] [selection]\n");
		log("\n");
		log("This command exposes all selected internal signals of a module as additional\n");
		log("outputs.\n");
		log("\n");
		log("    -dff\n");
		log("        only consider wires that are directly driven by register cell.\n");
		log("\n");
		log("    -cut\n");
		log("        when exposing a wire, create an input/output pair and cut the internal\n");
		log("        signal path at that wire.\n");
		log("\n");
		log("    -shared\n");
		log("        only expose those signals that are shared ammong the selected modules.\n");
		log("        this is useful for preparing modules for equivialence checking.\n");
		log("\n");
		log("    -evert\n");
		log("        also turn connections to instances of other modules to additional\n");
		log("        inputs and outputs and remove the module instances.\n");
		log("\n");
		log("    -evert-dff\n");
		log("        turn flip-flops to sets of inputs and outputs.\n");
		log("\n");
		log("    -sep <separator>\n");
		log("        when creating new wire/port names, the original object name is suffixed\n");
		log("        with this separator (default: '.') and the port name or a type\n");
		log("        designator for the exposed signal.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_shared = false;
		bool flag_evert = false;
		bool flag_dff = false;
		bool flag_cut = false;
		bool flag_evert_dff = false;
		std::string sep = ".";

		log_header("Executing EXPOSE pass (exposing internal signals as outputs).\n");

		size_t argidx;
		for (argidx = 1; argidx < args.size(); argidx++)
		{
			if (args[argidx] == "-shared") {
				flag_shared = true;
				continue;
			}
			if (args[argidx] == "-evert") {
				flag_evert = true;
				continue;
			}
			if (args[argidx] == "-dff") {
				flag_dff = true;
				continue;
			}
			if (args[argidx] == "-cut") {
				flag_cut = true;
				continue;
			}
			if (args[argidx] == "-evert-dff") {
				flag_evert_dff = true;
				continue;
			}
			if (args[argidx] == "-sep" && argidx+1 < args.size()) {
				sep = args[++argidx];
				continue;
			}
			break;
		}
		extra_args(args, argidx, design);

		CellTypes ct(design);

		std::map<RTLIL::Module*, std::map<std::string, dff_map_info_t>> dff_dq_maps;
		std::map<RTLIL::Module*, std::set<std::string>> dff_cells;

		if (flag_evert_dff)
		{
			RTLIL::Module *first_module = NULL;
			std::set<std::string> shared_dff_wires;

			for (auto &mod_it : design->modules)
			{
				if (!design->selected(mod_it.second))
					continue;

				create_dff_dq_map(dff_dq_maps[mod_it.second], design, mod_it.second);

				if (!flag_shared)
					continue;

				if (first_module == NULL) {
					for (auto &it : dff_dq_maps[mod_it.second])
						shared_dff_wires.insert(it.first);
					first_module = mod_it.second;
				} else {
					std::set<std::string> new_shared_dff_wires;
					for (auto &it : shared_dff_wires) {
						if (!dff_dq_maps[mod_it.second].count(it))
							continue;
						if (!compare_wires(first_module->wires.at(it), mod_it.second->wires.at(it)))
							continue;
						new_shared_dff_wires.insert(it);
					}
					shared_dff_wires.swap(new_shared_dff_wires);
				}
			}

			if (flag_shared)
				for (auto &map_it : dff_dq_maps)
				{
					std::map<std::string, dff_map_info_t> new_map;
					for (auto &it : map_it.second)
						if (shared_dff_wires.count(it.first))
							new_map[it.first] = it.second;
					map_it.second.swap(new_map);
				}

			for (auto &it1 : dff_dq_maps)
			for (auto &it2 : it1.second)
			for (auto &it3 : it2.second.cells)
				dff_cells[it1.first].insert(it3);
		}

		std::set<std::string> shared_wires, shared_cells;
		std::set<std::string> used_names;

		if (flag_shared)
		{
			RTLIL::Module *first_module = NULL;

			for (auto &mod_it : design->modules)
			{
				RTLIL::Module *module = mod_it.second;

				if (!design->selected(module))
					continue;

				std::set<std::string> dff_wires;
				if (flag_dff)
					find_dff_wires(dff_wires, module);

				if (first_module == NULL)
				{
					for (auto &it : module->wires)
						if (design->selected(module, it.second) && consider_wire(it.second, dff_dq_maps[module]))
							if (!flag_dff || dff_wires.count(it.first))
								shared_wires.insert(it.first);

					if (flag_evert)
						for (auto &it : module->cells)
							if (design->selected(module, it.second) && consider_cell(design, dff_cells[module], it.second))
								shared_cells.insert(it.first);

					first_module = module;
				}
				else
				{
					std::vector<std::string> delete_shared_wires, delete_shared_cells;

					for (auto &it : shared_wires)
					{
						RTLIL::Wire *wire;

						if (module->wires.count(it) == 0)
							goto delete_shared_wire;

						wire = module->wires.at(it);

						if (!design->selected(module, wire))
							goto delete_shared_wire;
						if (!consider_wire(wire, dff_dq_maps[module]))
							goto delete_shared_wire;
						if (!compare_wires(first_module->wires.at(it), wire))
							goto delete_shared_wire;
						if (flag_dff && !dff_wires.count(it))
							goto delete_shared_wire;

						if (0)
					delete_shared_wire:
							delete_shared_wires.push_back(it);
					}

					if (flag_evert)
						for (auto &it : shared_cells)
						{
							RTLIL::Cell *cell;

							if (module->cells.count(it) == 0)
								goto delete_shared_cell;

							cell = module->cells.at(it);

							if (!design->selected(module, cell))
								goto delete_shared_cell;
							if (!consider_cell(design, dff_cells[module], cell))
								goto delete_shared_cell;
							if (!compare_cells(first_module->cells.at(it), cell))
								goto delete_shared_cell;

							if (0)
						delete_shared_cell:
								delete_shared_cells.push_back(it);
						}

					for (auto &it : delete_shared_wires)
						shared_wires.erase(it);
					for (auto &it : delete_shared_cells)
						shared_cells.erase(it);
				}
			}
		}

		for (auto &mod_it : design->modules)
		{
			RTLIL::Module *module = mod_it.second;

			if (!design->selected(module))
				continue;

			std::set<std::string> dff_wires;
			if (flag_dff && !flag_shared)
				find_dff_wires(dff_wires, module);

			SigMap sigmap(module);

			SigMap out_to_in_map;
			std::vector<RTLIL::Wire*> new_wires;

			for (auto &it : module->wires)
			{
				if (flag_shared) {
					if (shared_wires.count(it.first) == 0)
						continue;
				} else {
					if (!design->selected(module, it.second) || !consider_wire(it.second, dff_dq_maps[module]))
						continue;
					if (flag_dff && !dff_wires.count(it.first))
						continue;
				}

				if (!it.second->port_output) {
					it.second->port_output = true;
					log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(it.second->name));
				}

				if (flag_cut) {
					RTLIL::Wire *in_wire = new RTLIL::Wire;
					in_wire->name = it.second->name + sep + "i";
					in_wire->width = it.second->width;
					in_wire->port_input = true;
					out_to_in_map.add(sigmap(it.second), in_wire);
					new_wires.push_back(in_wire);
				}
			}

			if (flag_cut)
			{
				for (auto it : new_wires)
					add_new_wire(module, it);

				for (auto &it : module->cells) {
					if (!ct.cell_known(it.second->type))
						continue;
					for (auto &conn : it.second->connections)
						if (ct.cell_input(it.second->type, conn.first))
							conn.second = out_to_in_map(sigmap(conn.second));
				}

				for (auto &conn : module->connections)
					conn.second = out_to_in_map(sigmap(conn.second));
			}

			std::set<RTLIL::SigBit> set_q_bits;

			for (auto &dq : dff_dq_maps[module])
			{
				if (!module->wires.count(dq.first))
					continue;

				RTLIL::Wire *wire = module->wires.at(dq.first);
				std::set<RTLIL::SigBit> wire_bits_set = sigmap(wire).to_sigbit_set();
				std::vector<RTLIL::SigBit> wire_bits_vec = sigmap(wire).to_sigbit_vector();

				dff_map_info_t &info = dq.second;

				RTLIL::Wire *wire_dummy_q = new RTLIL::Wire;
				wire_dummy_q->name = NEW_ID;
				wire_dummy_q->width = 0;
				add_new_wire(module, wire_dummy_q);

				for (auto &cell_name : info.cells) {
					RTLIL::Cell *cell = module->cells.at(cell_name);
					std::vector<RTLIL::SigBit> cell_q_bits = sigmap(cell->connections.at("\\Q")).to_sigbit_vector();
					for (auto &bit : cell_q_bits)
						if (wire_bits_set.count(bit))
							bit = RTLIL::SigBit(wire_dummy_q, wire_dummy_q->width++);
					cell->connections.at("\\Q") = cell_q_bits;
				}

				RTLIL::Wire *wire_q = new RTLIL::Wire;
				wire_q->name = wire->name + sep + "q";
				wire_q->width = wire->width;
				wire_q->port_input = true;
				log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire_q->name));
				add_new_wire(module, wire_q);

				RTLIL::SigSig connect_q;
				for (size_t i = 0; i < wire_bits_vec.size(); i++) {
					if (set_q_bits.count(wire_bits_vec[i]))
						continue;
					connect_q.first.append(wire_bits_vec[i]);
					connect_q.second.append(RTLIL::SigBit(wire_q, i));
					set_q_bits.insert(wire_bits_vec[i]);
				}
				module->connections.push_back(connect_q);

				RTLIL::Wire *wire_d = new RTLIL::Wire;
				wire_d->name = wire->name + sep + "d";
				wire_d->width = wire->width;
				wire_d->port_output = true;
				log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire_d->name));
				add_new_wire(module, wire_d);
				module->connections.push_back(RTLIL::SigSig(wire_d, info.sig_d));

				RTLIL::Wire *wire_c = new RTLIL::Wire;
				wire_c->name = wire->name + sep + "c";
				wire_c->port_output = true;
				log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire_c->name));
				add_new_wire(module, wire_c);
				if (info.clk_polarity) {
					module->connections.push_back(RTLIL::SigSig(wire_c, info.sig_clk));
				} else {
					RTLIL::Cell *c = new RTLIL::Cell;
					c->name = NEW_ID;
					c->type = "$not";
					c->parameters["\\A_SIGNED"] = 0;
					c->parameters["\\A_WIDTH"] = 1;
					c->parameters["\\Y_WIDTH"] = 1;
					c->connections["\\A"] = info.sig_clk;
					c->connections["\\Y"] = wire_c;
					module->add(c);
				}

				if (info.sig_arst != RTLIL::State::Sm)
				{
					RTLIL::Wire *wire_r = new RTLIL::Wire;
					wire_r->name = wire->name + sep + "r";
					wire_r->port_output = true;
					log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire_r->name));
					add_new_wire(module, wire_r);
					if (info.arst_polarity) {
						module->connections.push_back(RTLIL::SigSig(wire_r, info.sig_arst));
					} else {
						RTLIL::Cell *c = new RTLIL::Cell;
						c->name = NEW_ID;
						c->type = "$not";
						c->parameters["\\A_SIGNED"] = 0;
						c->parameters["\\A_WIDTH"] = 1;
						c->parameters["\\Y_WIDTH"] = 1;
						c->connections["\\A"] = info.sig_arst;
						c->connections["\\Y"] = wire_r;
						module->add(c);
					}

					RTLIL::Wire *wire_v = new RTLIL::Wire;
					wire_v->name = wire->name + sep + "v";
					wire_v->width = wire->width;
					wire_v->port_output = true;
					log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(wire_v->name));
					add_new_wire(module, wire_v);
					module->connections.push_back(RTLIL::SigSig(wire_v, info.arst_value));
				}
			}

			if (flag_evert)
			{
				std::vector<std::string> delete_cells;

				for (auto &it : module->cells)
				{
					if (flag_shared) {
						if (shared_cells.count(it.first) == 0)
							continue;
					} else {
						if (!design->selected(module, it.second) || !consider_cell(design, dff_cells[module], it.second))
							continue;
					}

					RTLIL::Cell *cell = it.second;

					if (design->modules.count(cell->type))
					{
						RTLIL::Module *mod = design->modules.at(cell->type);

						for (auto &it : mod->wires)
						{
							RTLIL::Wire *p = it.second;
							if (!p->port_input && !p->port_output)
								continue;

							RTLIL::Wire *w = new RTLIL::Wire;
							w->name = cell->name + sep + RTLIL::unescape_id(p->name);
							w->width = p->width;
							if (p->port_input)
								w->port_output = true;
							if (p->port_output)
								w->port_input = true;
							add_new_wire(module, w);

							log("New module port: %s/%s (%s)\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(w->name), RTLIL::id2cstr(cell->type));

							RTLIL::SigSpec sig;
							if (cell->connections.count(p->name) != 0)
								sig = cell->connections.at(p->name);
							sig.extend(w->width);
							if (w->port_input)
								module->connections.push_back(RTLIL::SigSig(sig, w));
							else
								module->connections.push_back(RTLIL::SigSig(w, sig));
						}
					}
					else
					{
						for (auto &it : cell->connections)
						{
							RTLIL::Wire *w = new RTLIL::Wire;
							w->name = cell->name + sep + RTLIL::unescape_id(it.first);
							w->width = it.second.width;
							if (ct.cell_input(cell->type, it.first))
								w->port_output = true;
							if (ct.cell_output(cell->type, it.first))
								w->port_input = true;
							add_new_wire(module, w);

							log("New module port: %s/%s (%s)\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(w->name), RTLIL::id2cstr(cell->type));

							if (w->port_input)
								module->connections.push_back(RTLIL::SigSig(it.second, w));
							else
								module->connections.push_back(RTLIL::SigSig(w, it.second));
						}
					}

					delete_cells.push_back(cell->name);
				}

				for (auto &it : delete_cells) {
					log("Removing cell: %s/%s (%s)\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(it), RTLIL::id2cstr(module->cells.at(it)->type));
					delete module->cells.at(it);
					module->cells.erase(it);
				}
			}

			module->fixup_ports();
		}
	}
} ExposePass;
 
