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
#include "kernel/rtlil.h"
#include "kernel/log.h"

static bool consider_wire(RTLIL::Wire *wire)
{
	if (wire->name[0] == '$')
		return false;
	if (wire->port_input)
		return false;
	return true;
}

static bool consider_cell(RTLIL::Design *design, RTLIL::Cell *cell)
{
	if (cell->name[0] == '$')
		return false;
	if (design->modules.count(cell->type) == 0)
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
		log("    -shared\n");
		log("        only expose those signals that are shared ammong the selected modules.\n");
		log("        this is useful for preparing modules for equivialence checking.\n");
		log("\n");
		log("    -evert\n");
		log("        also turn connections to instances of other modules to additional\n");
		log("        inputs and outputs and remove the module instances.\n");
		log("\n");
	}
	virtual void execute(std::vector<std::string> args, RTLIL::Design *design)
	{
		bool flag_shared = false;
		bool flag_evert = false;

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
			break;
		}
		extra_args(args, argidx, design);

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

				if (first_module == NULL)
				{
					for (auto &it : module->wires)
						if (design->selected(module, it.second) && consider_wire(it.second))
							shared_wires.insert(it.first);

					if (flag_evert)
						for (auto &it : module->cells)
							if (design->selected(module, it.second) && consider_cell(design, it.second))
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
						if (!consider_wire(wire))
							goto delete_shared_wire;
						if (!compare_wires(first_module->wires.at(it), wire))
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
							if (!consider_cell(design, cell))
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

			for (auto &it : module->wires)
			{
				if (flag_shared) {
					if (shared_wires.count(it.first) == 0)
						continue;
				} else {
					if (!design->selected(module, it.second) || !consider_wire(it.second))
						continue;
				}

				if (!it.second->port_output) {
					it.second->port_output = true;
					log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(it.second->name));
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
						if (!design->selected(module, it.second) || !consider_cell(design, it.second))
							continue;
					}

					RTLIL::Cell *cell = it.second;
					RTLIL::Module *mod = design->modules.at(cell->type);

					for (auto &it : mod->wires)
					{
						RTLIL::Wire *p = it.second;
						if (!p->port_input && !p->port_output)
							continue;

						RTLIL::Wire *w = new RTLIL::Wire;
						w->name = cell->name + "." + RTLIL::unescape_id(p->name);
						w->width = p->width;
						if (p->port_input)
							w->port_output = true;
						if (p->port_output)
							w->port_input = true;
						module->add(w);

						log("New module port: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(w->name));

						RTLIL::SigSpec sig;
						if (cell->connections.count(p->name) != 0)
							sig = cell->connections.at(p->name);
						sig.extend(w->width);
						if (w->port_input)
							module->connections.push_back(RTLIL::SigSig(sig, w));
						else
							module->connections.push_back(RTLIL::SigSig(w, sig));
					}

					delete_cells.push_back(cell->name);
				}

				for (auto &it : delete_cells) {
					log("Removing cell: %s/%s\n", RTLIL::id2cstr(module->name), RTLIL::id2cstr(it));
					delete module->cells.at(it);
					module->cells.erase(it);
				}
			}

			module->fixup_ports();
		}
	}
} ExposePass;
 
